{-# LANGUAGE GADTs, OverloadedStrings, FlexibleContexts #-}

module Main where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, hSetEncoding, stderr, stdin, utf8)
import Data.Maybe (isJust)
import qualified Data.ByteString.Lazy.Char8 as BL
import Control.Monad (msum)
import Data.Aeson (Value, object, (.=), encode)

import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Calculi.NaturalDeduction.Checker (ProofErrorMessage(..), Feedback(..), toDisplaySequence)
import Carnap.Calculi.Util (defaultRuntimeDeductionConfig)
import Carnap.Languages.PurePropositional.Logic (ofPropSys)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys)
import Carnap.Languages.PureSecondOrder.Logic (ofSecondOrderSys)
import Carnap.Languages.SetTheory.Logic (ofSetTheorySys)
import Carnap.Languages.DefiniteDescription.Logic.Gamut (ofDefiniteDescSys)
import Carnap.Languages.ModalPropositional.Logic (ofModalPropSys)

--------------------
--  CLI Parsing   --
--------------------

data Command = Help | ListSystems | ListRules String | Check String String

data OutputFormat = JSON | PlainText

main :: IO ()
main = do
    hSetEncoding stdin utf8
    args <- getArgs
    let fmt = if "--plain-text" `elem` args then PlainText else JSON
        args' = filter (/= "--plain-text") args
    case parseArgs args' of
        Left err -> do
            case fmt of
                JSON      -> BL.putStrLn $ encode $ object ["error" .= err]
                PlainText -> do
                    hPutStrLn stderr $ "Error: " ++ err
                    hPutStrLn stderr "Run with --help for usage."
            exitFailure
        Right Help ->
            putStr usage
        Right ListSystems -> case fmt of
            JSON      -> BL.putStrLn $ encode $ object ["systems" .= allSystemNames]
            PlainText -> mapM_ putStrLn allSystemNames
        Right (ListRules sys) ->
            case getRuleNames sys of
                Nothing -> die fmt $ "Unknown system: " ++ sys
                Just names -> case fmt of
                    JSON      -> BL.putStrLn $ encode $
                        object ["system" .= sys, "rules" .= names]
                    PlainText -> mapM_ putStrLn names
        Right (Check sys proofArg) -> do
            proofText <- if proofArg == "-"
                         then getContents
                         else return (unescape proofArg)
            case checkProof sys proofText of
                Nothing  -> die fmt $ "Unknown system: " ++ sys
                Just pr  -> case fmt of
                    JSON      -> BL.putStrLn $ encode $ proofResultToJSON pr
                    PlainText -> putStr $ proofResultToPlain pr

die :: OutputFormat -> String -> IO ()
die fmt msg = do
    case fmt of
        JSON      -> BL.putStrLn $ encode $ object ["error" .= msg]
        PlainText -> hPutStrLn stderr $ "Error: " ++ msg
    exitFailure

usage :: String
usage = unlines
    [ "Usage: carnap-cli [OPTIONS]"
    , ""
    , "Commands:"
    , "  --list-systems                   List all supported logic systems"
    , "  --list-rules <system>            List valid rule names for a system"
    , "  --system <name> --proof <text>   Check a proof (use - for stdin)"
    , ""
    , "Options:"
    , "  --plain-text                     Output plain text instead of JSON"
    , "  --help, -h                       Show this help message"
    ]

parseArgs :: [String] -> Either String Command
parseArgs args
    | "--help" `elem` args || "-h" `elem` args = Right Help
    | "--list-systems" `elem` args = Right ListSystems
    | otherwise = case lookupArg "--list-rules" args of
        Just sys -> Right (ListRules sys)
        Nothing  -> case (lookupArg "--system" args, lookupArg "--proof" args) of
            (Nothing, _) -> Left "Missing required argument: --system <name>"
            (_, Nothing) -> Left "Missing required argument: --proof <text>"
            (Just sys, Just proof) -> Right (Check sys proof)

lookupArg :: String -> [String] -> Maybe String
lookupArg _ []       = Nothing
lookupArg _ [_]      = Nothing
lookupArg key (x:y:rest)
    | x == key  = Just y
    | otherwise = lookupArg key (y:rest)

-- Replace literal \n sequences with newlines in command-line proof text
unescape :: String -> String
unescape []                = []
unescape ('\\':'n':rest)   = '\n' : unescape rest
unescape ('\\':'\\':rest)  = '\\' : unescape rest
unescape (c:rest)          = c : unescape rest

----------------------------
--  Proof Result Type     --
----------------------------

data ProofResult = ProofResult
    { prSystem  :: String
    , prSuccess :: Bool
    , prSequent :: Maybe String
    , prLines   :: [(Int, LineStatus)]
    }

data LineStatus = Ok | Blank | LineError String

--------------------------
--  Proof Checking API  --
--------------------------

-- Try each system dispatcher in sequence. The first match wins.
checkProof :: String -> String -> Maybe ProofResult
checkProof sys proofText = msum
    [ ofPropSys         (runCheck sys proofText) sys
    , ofFOLSys          (runCheck sys proofText) sys
    , ofSecondOrderSys  (runCheck sys proofText) sys
    , ofSetTheorySys    (runCheck sys proofText) sys
    , ofDefiniteDescSys (runCheck sys proofText) sys
    , ofModalPropSys    (runCheck sys proofText) sys
    ]

-- Look up valid rule names for a system.
getRuleNames :: String -> Maybe [String]
getRuleNames sys = msum
    [ ofPropSys         ndRuleNames sys
    , ofFOLSys          ndRuleNames sys
    , ofSecondOrderSys  ndRuleNames sys
    , ofSetTheorySys    ndRuleNames sys
    , ofDefiniteDescSys ndRuleNames sys
    , ofModalPropSys    ndRuleNames sys
    ]

-- Core proof-checking logic. No type signature — GHC infers a polymorphic
-- type compatible with all dispatcher continuations. Same proof-checking
-- pattern as Carnap/test/test.hs lines 89-92.
runCheck sys proofText ndcalc =
    let ded = ndParseProof ndcalc defaultRuntimeDeductionConfig proofText
        Feedback mseq ds = toDisplaySequence (ndProcessLine ndcalc) ded
        notation = ndNotation ndcalc
        success = isJust mseq && all lineOk ds
        seqStr = fmap (notation . show) mseq
        lineStatuses = zipWith (toLineStatus notation) [1 :: Int ..] ds
    in ProofResult sys success seqStr lineStatuses

toLineStatus :: (String -> String) -> Int -> Either (ProofErrorMessage lex) a -> (Int, LineStatus)
toLineStatus _ n (Right _)           = (n, Ok)
toLineStatus _ n (Left (NoResult _)) = (n, Blank)
toLineStatus notation n (Left err)   = (n, LineError (renderError notation err))

-- Blank lines (NoResult) are not errors — same treatment as test.hs
lineOk :: Either (ProofErrorMessage lex) a -> Bool
lineOk (Right _)              = True
lineOk (Left (NoResult _))    = True
lineOk _                      = False

renderError :: (String -> String) -> ProofErrorMessage lex -> String
renderError _ (NoParse e _)          = "Parse error: " ++ show e
renderError _ (NoUnify _ n)          = "Could not unify on line " ++ show n
renderError notation (GenericError s _) = notation s
renderError _ (NoResult _)           = ""

-----------------------
--  JSON Rendering   --
-----------------------

proofResultToJSON :: ProofResult -> Value
proofResultToJSON pr = object $
    [ "system"  .= prSystem pr
    , "success" .= prSuccess pr
    , "lines"   .= map lineStatusToJSON (prLines pr)
    ] ++ maybe [] (\s -> ["sequent" .= s]) (prSequent pr)

lineStatusToJSON :: (Int, LineStatus) -> Value
lineStatusToJSON (n, Ok) =
    object ["line" .= n, "status" .= ("ok" :: String)]
lineStatusToJSON (n, Blank) =
    object ["line" .= n, "status" .= ("blank" :: String)]
lineStatusToJSON (n, LineError msg) =
    object [ "line" .= n
           , "status" .= ("error" :: String)
           , "message" .= msg
           ]

-----------------------------
--  Plain Text Rendering   --
-----------------------------

proofResultToPlain :: ProofResult -> String
proofResultToPlain pr = unlines $
    [ "System:  " ++ prSystem pr ] ++
    maybe [] (\s -> ["Sequent: " ++ s]) (prSequent pr) ++
    [""] ++
    map linePlain (prLines pr) ++
    [""] ++
    [if prSuccess pr then "Result: correct" else "Result: INVALID"]

linePlain :: (Int, LineStatus) -> String
linePlain (n, Ok)           = "  " ++ padNum n ++ "  ok"
linePlain (n, Blank)        = "  " ++ padNum n ++ "  (blank)"
linePlain (n, LineError msg) = "  " ++ padNum n ++ "  ERROR: " ++ msg

padNum :: Int -> String
padNum n = let s = show n in replicate (3 - length s) ' ' ++ s

----------------------------
--  Known System Names    --
----------------------------

allSystemNames :: [String]
allSystemNames = concat
    [ -- Propositional (ofPropSys)
      [ "LogicBookSD", "LogicBookSDPlus"
      , "allenSL", "allenSLPlus"
      , "arthurSL"
      , "belotSD", "belotSDPlus"
      , "bonevacSL"
      , "cortensSL"
      , "davisSL"
      , "ebelsDugganTFL"
      , "gallowSL", "gallowSLPlus"
      , "gamutIPND", "gamutMPND", "gamutPND", "gamutPNDPlus"
      , "goldfarbPropND"
      , "gregorySD", "gregorySDE"
      , "hardegreeSL", "hardegreeSL2006"
      , "hausmanSL"
      , "howardSnyderSL"
      , "hurleySL"
      , "ichikawaJenkinsSL"
      , "johnsonSL", "johnsonSLPlus"
      , "landeProp"
      , "lemmonProp"
      , "magnusSL", "magnusSLPlus"
      , "montagueSC"
      , "prop", "propStrict", "propNonC", "propNL", "propNLStrict"
      , "thomasBolducAndZachTFL", "thomasBolducAndZachTFL2019", "thomasBolducAndZachTFLCore"
      , "ravenTFL", "ravenTFL2019", "ravenTFLCore"
      , "tomassiPL"
      , "winklerTFL"
      , "zachPropEq"
      ]
    , -- First-order (ofFOLSys)
      [ "LogicBookPD", "LogicBookPDE", "LogicBookPDEPlus", "LogicBookPDPlus"
      , "arthurQL"
      , "belotPD", "belotPDE", "belotPDEPlus", "belotPDPlus"
      , "bonevacQL"
      , "cortensQL"
      , "davisQL"
      , "ebelsDugganFOL"
      , "firstOrder", "firstOrderNonC"
      , "gallowPL", "gallowPLPlus"
      , "gamutND", "gamutNDPlus"
      , "goldfarbAltND", "goldfarbAltNDPlus", "goldfarbND", "goldfarbNDPlus"
      , "gregoryPD", "gregoryPDE"
      , "hardegreePL", "hardegreePL2006"
      , "hausmanPL"
      , "howardSnyderPL"
      , "hurleyPL"
      , "ichikawaJenkinsQL"
      , "lemmonQuant", "landeQuant"
      , "magnusQL", "magnusQLPlus"
      , "montagueQC"
      , "ravenFOL", "ravenFOL2019", "ravenFOLCore", "ravenFOLPlus2019"
      , "thomasBolducAndZachFOL", "thomasBolducAndZachFOL2019"
      , "thomasBolducAndZachFOLCore", "thomasBolducAndZachFOLPlus2019"
      , "tomassiQL"
      , "winklerFOL"
      , "zachFOLEq"
      ]
    , -- Second-order (ofSecondOrderSys)
      [ "secondOrder", "polyadicSecondOrder", "gamutNDSOL" ]
    , -- Set theory (ofSetTheorySys)
      [ "elementarySetTheory", "separativeSetTheory" ]
    , -- Definite descriptions (ofDefiniteDescSys)
      [ "gamutNDDesc" ]
    , -- Modal propositional (ofModalPropSys)
      [ "hardegreeL", "hardegreeK", "hardegreeD", "hardegreeT"
      , "hardegreeB", "hardegree4", "hardegree5", "hardegreeWTL"
      ]
    ]
