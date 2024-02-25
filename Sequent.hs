{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# LANGUAGE InstanceSigs #-}

module Sequent(
    Sequent(..),
) where
import Data.List (intercalate)

-- class Sequent p where
--   freeVars :: [Formula p]
--   freeVars = []

--   premises :: p -> [Formula p]
--   consequent :: p -> Formula p

data Sequent p = [p] `Entails` p
               | p `Biconditional` p
             deriving (Read)

instance Show a => Show (Sequent a) where
  show :: Sequent a -> String
  show (antecedents `Entails` consequent) = 
    intercalate ", " [show antecedents] ++ " ⊢ " ++ show consequent
  show (antecedent `Biconditional` consequent) = 
    show antecedent ++ " ⟛ " ++ show consequent
