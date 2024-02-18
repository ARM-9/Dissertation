{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Formula(
    Formula(..)
) where

import Parser
import Sequent
import Control.Applicative

class Formula p where
    formulaP :: Parser p
    
    evalF :: String -> Either String p
    evalF = eval formulaP

    sequentP :: Parser (Sequent p)
    sequentP = do l <- formulaP
                  do symbol "|-" <|> symbol "⊢"
                     r <- formulaP
                     return ([l] `Entails` r)
                   <|> do symbol "-||-" <|> symbol "⟛"
                          r <- formulaP
                          return (l `Biconditional` r)
               <|> do ls <- list formulaP
                      symbol "|-" <|> symbol "⊢"
                      r <- formulaP
                      return (ls `Entails` r)
               <|> do symbol "|-" <|> symbol "⊢"
                      r <- formulaP
                      return ([] `Entails` r)
    
    evalS :: String -> Either String (Sequent p)
    evalS = eval sequentP
