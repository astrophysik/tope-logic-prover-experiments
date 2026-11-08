{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (filterM)
import Data.Aeson (Value (Array, Object, String))
import qualified Data.Aeson.Key as Key
import qualified Data.Aeson.KeyMap as KeyMap
import Data.Foldable (toList)
import qualified Data.Yaml as Yaml
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.Exit (ExitCode (..))
import System.FilePath (takeExtension, (</>))
import System.Process (readProcessWithExitCode)
import Test.Hspec (Spec, describe, expectationFailure, hspec, it, runIO, shouldBe)
import qualified Data.Text as Text

testCorpusFilePath :: FilePath
testCorpusFilePath = "test/corpus/topes"

findCorpusYamlFiles :: FilePath -> IO [FilePath]
findCorpusYamlFiles path = do
  directoryList <- map (path </>) <$> listDirectory path
  subDirectories <- filterM doesDirectoryExist directoryList
  innerTests <- mapM findCorpusYamlFiles subDirectories
  files <- filter (\file -> (takeExtension file) == ".yaml") <$> filterM doesFileExist directoryList
  pure $ (concat innerTests) ++ files

lookupField :: String -> KeyMap.KeyMap Value -> Maybe Value
lookupField field object =
  KeyMap.lookup (Key.fromString field) object

requireField :: String -> KeyMap.KeyMap Value -> Either String Value
requireField field object =
  case lookupField field object of
    Just value -> Right value
    Nothing -> Left ("Missing " ++ field ++ " field")

requireObjectField :: String -> KeyMap.KeyMap Value -> Either String (KeyMap.KeyMap Value)
requireObjectField field object = do
  value <- requireField field object
  case value of
    Object fieldObject -> Right fieldObject
    _ -> Left (field ++ " field must be a YAML object")

requireStringField :: String -> KeyMap.KeyMap Value -> Either String ()
requireStringField field object = do
  value <- requireField field object
  case value of
    String _ -> Right ()
    _ -> Left (field ++ " field must be a string")

requireStringArrayField :: String -> KeyMap.KeyMap Value -> Either String ()
requireStringArrayField field object = do
  value <- requireField field object
  case value of
    Array values
      | all isStringValue (toList values) -> Right ()
      | otherwise -> Left (field ++ " field must contain only strings")
    _ -> Left (field ++ " field must be a YAML array")

requireOneOfStringField :: String -> [String] -> KeyMap.KeyMap Value -> Either String ()
requireOneOfStringField field allowedValues object = do
  value <- requireField field object
  case value of
    String text
      | Key.toString (Key.fromText text) `elem` allowedValues -> Right ()
      | otherwise ->
          Left
            ( field
                ++ " field must be one of: "
                ++ commaSeparated allowedValues
            )
    _ -> Left (field ++ " field must be a string")

isStringValue :: Value -> Bool
isStringValue value =
  case value of
    String _ -> True
    _ -> False

commaSeparated :: [String] -> String
commaSeparated [] = ""
commaSeparated [value] = value
commaSeparated (value : values) = value ++ concatMap (", " ++) values

validateSequentTest :: Value -> Value -> Either String ()
validateSequentTest input expected = do
  sequentInput <- requireObject "input" input
  requireStringArrayField "context" sequentInput
  requireStringArrayField "hypotheses" sequentInput
  requireStringField "goal" sequentInput

  sequentExpected <- requireObject "expected" expected
  requireOneOfStringField "entailment" ["derivable", "underivable", "unsolved"] sequentExpected
  requireOneOfStringField
    "premises_consistency"
    ["consistent", "inconsistent"]
    sequentExpected

validateRzkTest :: Value -> Value -> Either String ()
validateRzkTest input expected = do
  rzkInput <- requireObject "input" input
  requireStringField "rzk" rzkInput

  rzkExpected <- requireObject "expected" expected
  requireOneOfStringField "typechecks" ["accepted", "rejected"] rzkExpected
  case lookupField "typechecks" rzkExpected of
    Just (String "rejected") ->
      requireStringField "error_contains" rzkExpected
    _ ->
      Right ()

validateDiagramGoalTest :: Value -> Value -> Either String ()
validateDiagramGoalTest input expected = do
  diagramInput <- requireObject "input" input
  requireStringArrayField "context" diagramInput
  requireStringArrayField "premises" diagramInput
  requireStringField "goal" diagramInput

  diagramExpected <- requireObject "expected" expected
  requireOneOfStringField "classification" ["diagram", "non-diagram"] diagramExpected

requireObject :: String -> Value -> Either String (KeyMap.KeyMap Value)
requireObject label value =
  case value of
    Object object -> Right object
    _ -> Left (label ++ " must be a YAML object")

validateCorpusObject :: KeyMap.KeyMap Value -> Either String ()
validateCorpusObject object = do
  requireStringField "id" object
  requireStringField "kind" object
  requireStringField "source" object
  requireStringArrayField "tags" object
  provenance <- requireObjectField "provenance" object
  requireStringField "kind" provenance
  input <- requireField "input" object
  expected <- requireField "expected" object
  case lookupField "kind" object of
    Just (String "sequent") -> validateSequentTest input expected
    Just (String "rzk") -> validateRzkTest input expected
    Just (String "diagram-goal") -> validateDiagramGoalTest input expected
    Just (String _) -> Left "kind field must be one of: sequent, rzk, diagram-goal"
    Just _ -> Left "kind field must be a string"
    Nothing -> Left "Missing kind field"

corpusFileSpec :: FilePath -> Spec
corpusFileSpec path = do
  it path $ do
    result <- Yaml.decodeFileEither path
    case result of
      Left err ->
        expectationFailure (Yaml.prettyPrintParseException err)
      Right (Object object) -> do
        case validateCorpusObject object of
          Left message -> expectationFailure message
          Right () ->
            case (lookupField "kind" object, lookupField "source" object) of
              (Just (String "sequent"), Just (String "topes")) ->
                case requireObjectField "expected" object of
                  Left message -> expectationFailure message
                  Right expectedObject ->
                    case lookupField "entailment" expectedObject of
                      Just (String entailment) -> do
                        (exitCode, output, errors) <- readProcessWithExitCode "python3" ["scripts/oracle.py", path] ""
                        case exitCode of 
                          ExitSuccess -> 
                            case lines output of
                              actual : _ -> actual `shouldBe` Text.unpack entailment
                              [] -> expectationFailure "Oracle produced no verdict"
                          ExitFailure _ -> 
                              expectationFailure $ "Got error during work " ++ errors
                      _ -> expectationFailure "Missing expected.entailment"
              _ -> pure ()
      Right _ ->
        expectationFailure "Expected top-level YAML object"

spec :: Spec
spec = do
  corpusFiles <- runIO $ findCorpusYamlFiles testCorpusFilePath
  describe "test corpus format" $ do
    mapM_ corpusFileSpec corpusFiles

main :: IO ()
main = hspec spec
