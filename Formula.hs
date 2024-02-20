{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Formula(
    Formula(..)
) where

import Parser
import Sequent
import Control.Applicative

class Formula p where
    const :: Bool -> p
    not :: p -> p
    and :: p -> p -> p
    or :: p -> p -> p
    imp :: p -> p -> p
    equi :: p -> p -> p

    formulaP :: Parser p
    
    evalF :: String -> Either String p
    evalF = eval formulaP

    sequentP :: Parser (Sequent p)
    
    evalS :: String -> Either String (Sequent p)
    evalS = eval sequentP
