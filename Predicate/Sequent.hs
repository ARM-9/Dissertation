module Predicate.Sequent(
  Sequent(..),
  isTrivial,
  getSequent
) where

import Predicate.Symbol
import Parser
import Predicate.Term
import Predicate.Pred
import Data.List
import Control.Applicative
import Utils

-- [recognised variables]
data Sequent = ([Variable], [Pred]) `Entails` Pred
             | ([Variable], Pred) `Equivalent` Pred

instance Show Sequent where
  show :: Sequent -> String
  show ((vs, hypotheses) `Entails` conclusion) =
    show vs ++ intercalate ", " (map show hypotheses) ++ " ⊢ " ++ show conclusion
  show ((_, hypothesis) `Equivalent` conclusion) =
    show hypothesis ++ " ⟛ " ++ show conclusion

addVarsToSeq :: Sequent -> Sequent
addVarsToSeq ((_, as) `Entails` c) =
  (nub $ concatMap vars as ++ vars c, as) `Entails` c
addVarsToSeq ((_, a) `Equivalent` c) =
  (nub $ vars a ++ vars c, a) `Equivalent` c

-- Evaluates if a sequent has been proven
-- by verifying that the conclusion has
-- been derived from the hypotheses
isTrivial :: Sequent -> Bool
isTrivial ((_, as) `Entails` c) = c `elem` as

sequentP :: [Symbol] -> Parser Sequent
sequentP syms = do l <- predP syms
                   do symbol "|-" <|> symbol "⊢"
                      r <- predP syms
                      return (([], [l]) `Entails` r)
                    <|> do symbol "-||-" <|> symbol "⟛"
                           r <- predP syms
                           return (([], l) `Equivalent` r)
                <|> do ls <- list $ predP syms
                       symbol "|-" <|> symbol "⊢"
                       r <- predP syms
                       return (([], ls) `Entails` r)
                <|> do symbol "|-" <|> symbol "⊢"
                       r <- predP syms
                       return (([], []) `Entails` r)

evalS :: [Symbol] -> String -> Either String Sequent
evalS syms = eval (sequentP syms)

getSequent :: [Symbol] -> IO Sequent
getSequent syms = do xs <- prompt "Input a sequent: "
                     let s = evalS syms xs
                     case s of
                        (Right s) -> return $ addVarsToSeq s
                        (Left errMsg) -> putStrLn errMsg >> getSequent syms