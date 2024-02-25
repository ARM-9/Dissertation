{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Formula(
    Formula(..)
) where

import Propositional
import Predicate

data Formula = PropFormula Prop | PredFormula Pred