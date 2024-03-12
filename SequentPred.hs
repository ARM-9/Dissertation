module Sequent(
  Sequent,
  evalS
) where

import Symbol
import Parser
import Term
import Pred
import Data.List
import Control.Applicative

data Sequent = ([Term], [Pred]) `Entails` Pred
             | ([Term], Pred) `Biconditional` Pred

-- TODO: make a pretty print for sequents
instance Show Sequent where
  show :: Sequent -> String
  show ((_, antecedents) `Entails` consequent) =
    intercalate ", " [show antecedents] ++ " ⊢ " ++ show consequent
  show ((_, antecedent) `Biconditional` consequent) =
    show antecedent ++ " ⟛ " ++ show consequent

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