module Prover.G4ip
  ( g4ipProver,
  )
where

import Corpus (SequentCase (..))
import Data.Char (toLower)
import qualified G4ipProver.Parser as G4ipParser
import qualified G4ipProver.Proposition as G4ipProp
import qualified G4ipProver.Prover as G4ipProver
import qualified G4ipProver.TopeParser as TopeParser
import Prover.Interface (Prover (..), ProverResult (..))

g4ipProver :: Prover
g4ipProver =
  Prover
    { proverName = "g4ip",
      proveSequent = proveWithG4ip
    }

proveWithG4ip :: SequentCase -> ProverResult
proveWithG4ip sequent =
  case parseSequent sequent of
    Left err -> ProverUnsupported err
    Right (parsedHypotheses, parsedGoal) ->
      case G4ipProver.proveSequent parsedHypotheses parsedGoal of
        Just _ -> ProverDerivable
        Nothing -> ProverUnderivable

parseSequent :: SequentCase -> Either String ([G4ipProp.Prop], G4ipProp.Prop)
parseSequent sequent
  | source sequent == "topes" || not (null (context sequent)) =
      TopeParser.parseTopeSequent (context sequent) (hypotheses sequent) (goal sequent)
  | otherwise = do
      parsedHypotheses <- traverse parseCorpusFormula (hypotheses sequent)
      parsedGoal <- parseCorpusFormula (goal sequent)
      pure (parsedHypotheses, parsedGoal)

parseCorpusFormula :: String -> Either String G4ipProp.Prop
parseCorpusFormula formula =
  case G4ipParser.parseProp (normalizeFormula formula) of
    Left err -> Left ("cannot parse formula " ++ show formula ++ ": " ++ err)
    Right parsed -> Right parsed

normalizeFormula :: String -> String
normalizeFormula =
  concatMap normalizeChar
  where
    normalizeChar char =
      case char of
        '¬' -> "~"
        '∧' -> "/\\"
        '∨' -> "\\/"
        '→' -> "->"
        '↔' -> "<=>"
        '⊤' -> "T"
        '⊥' -> "F"
        other -> [toLower other]
