module Predicate.Sequent(
  Sequent(..),
  evalS,
  getSequent
) where

import Predicate.Symbol
import Parser
import Predicate.Term
import Predicate.Pred
import Data.List
import Control.Applicative
import Utils

data Sequent = ([Term], [Pred]) `Entails` Pred
             | ([Term], Pred) `Biconditional` Pred

-- TODO: make a pretty print for sequents
instance Show Sequent where
  show :: Sequent -> String
  show ((_, antecedents) `Entails` consequent) =
    intercalate ", " [show antecedents] ++ " ⊢ " ++ show consequent
  show ((_, antecedent) `Biconditional` consequent) =
    show antecedent ++ " ⟛ " ++ show consequent

extractVars :: Sequent -> Sequent
extractVars ((_, as) `Entails` c) = (nub $ concatMap vars as ++ vars c, as) `Entails` c
extractVars ((_, a) `Biconditional` c) = (nub $ vars a ++ vars c, a) `Biconditional` c

sequentP :: [Symbol] -> Parser Sequent
sequentP syms = do l <- l1P syms
                   do symbol "|-" <|> symbol "⊢"
                      r <- l1P syms
                      return (([], [l]) `Entails` r)
                    <|> do symbol "-||-" <|> symbol "⟛"
                           r <- l1P syms
                           return (([], l) `Biconditional` r)
                <|> do ls <- list $ l1P syms
                       symbol "|-" <|> symbol "⊢"
                       r <- l1P syms
                       return (([], ls) `Entails` r)
                <|> do symbol "|-" <|> symbol "⊢"
                       r <- l1P syms
                       return (([], []) `Entails` r)

evalS :: [Symbol] -> String -> Either String Sequent
evalS syms = eval (sequentP syms)

getSequent :: [Symbol] -> String -> IO Sequent
getSequent syms p = do xs <- prompt p
                       let s = evalS syms xs
                       case s of
                         (Right s) -> return $ extractVars s
                         (Left errMsg) -> putStrLn errMsg >> getSequent syms p