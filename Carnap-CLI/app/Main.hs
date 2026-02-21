{-# LANGUAGE GADTs, OverloadedStrings, FlexibleContexts #-}

module Main where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hSetEncoding, stdin, utf8)
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

data Command = ListSystems | Check String String

main :: IO ()
main = do
    hSetEncoding stdin utf8
    args <- getArgs
    case parseArgs args of
        Left err -> dieJSON err
        Right ListSystems ->
            BL.putStrLn $ encode $ object ["systems" .= allSystemNames]
        Right (Check sys proofArg) -> do
            proofText <- if proofArg == "-"
                         then getContents
                         else return (unescape proofArg)
            case checkProof sys proofText of
                Nothing  -> dieJSON $ "Unknown system: " ++ sys
                Just val -> BL.putStrLn $ encode val

dieJSON :: String -> IO ()
dieJSON msg = do
    BL.putStrLn $ encode $ object ["error" .= msg]
    exitFailure

parseArgs :: [String] -> Either String Command
parseArgs args
    | "--list-systems" `elem` args = Right ListSystems
    | otherwise = case (lookupArg "--system" args, lookupArg "--proof" args) of
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

--------------------------
--  Proof Checking API  --
--------------------------

-- Try each system dispatcher in sequence. The first match wins.
checkProof :: String -> String -> Maybe Value
checkProof sys proofText = msum
    [ ofPropSys         (runCheck sys proofText) sys
    , ofFOLSys          (runCheck sys proofText) sys
    , ofSecondOrderSys  (runCheck sys proofText) sys
    , ofSetTheorySys    (runCheck sys proofText) sys
    , ofDefiniteDescSys (runCheck sys proofText) sys
    , ofModalPropSys    (runCheck sys proofText) sys
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
        lineResults = zipWith (renderLine notation) [1 :: Int ..] ds
    in object $ [ "system" .= sys
                , "success" .= success
                , "lines" .= lineResults
                ] ++ maybe [] (\s -> ["sequent" .= s]) seqStr

-- Blank lines (NoResult) are not errors — same treatment as test.hs
lineOk :: Either (ProofErrorMessage lex) a -> Bool
lineOk (Right _)              = True
lineOk (Left (NoResult _))    = True
lineOk _                      = False

-----------------------
--  JSON Rendering   --
-----------------------

renderLine :: (String -> String) -> Int -> Either (ProofErrorMessage lex) a -> Value
renderLine _ n (Right _) =
    object ["line" .= n, "status" .= ("ok" :: String)]
renderLine _ n (Left (NoResult _)) =
    object ["line" .= n, "status" .= ("blank" :: String)]
renderLine notation n (Left err) =
    object [ "line" .= n
           , "status" .= ("error" :: String)
           , "message" .= renderError notation err
           ]

renderError :: (String -> String) -> ProofErrorMessage lex -> String
renderError _ (NoParse e _)      = "Parse error: " ++ show e
renderError _ (NoUnify _ n)      = "Could not unify on line " ++ show n
renderError notation (GenericError s _) = notation s
renderError _ (NoResult _)       = ""

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
