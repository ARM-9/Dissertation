module Predicate.Term(
  Term(..),
  termP,
  evalT,
  varsT,
  subT,
  isFree,
  newFreeVar
) where

import Data.Char
import Predicate.Symbol
import Parser
import Control.Applicative
import Data.List
import Utils

data Term = Var    String
          | ConstT String
          | Func   String [Term]

instance Show Term where
  show :: Term -> String
  show (Var x)     = x
  show (ConstT x)  = x
  show (Func f xs) = f ++ prettyArgs xs

instance Eq Term where
  (==) :: Term -> Term -> Bool
  (Var x)     == (Var y)     = x == y
  (ConstT x)  == (ConstT y)  = x == y
  (Func f xs) == (Func g ys) = f == g && xs == ys
  _           == _           = False

termP :: [Symbol] -> Parser Term
termP syms = do f <- lowerStr
                case findSymbol f syms of
                     Just (Function _ arity) -> do symbol "("
                                                   ts <- listN arity $ termP syms
                                                   symbol ")"
                                                   return $ Func f ts
                     _                       -> empty
      <|> do x <- lowerStr
             case findSymbol x syms of
                  Nothing           -> return $ Var x
                  Just (Constant _) -> return $ ConstT x
                  _                 -> empty
      <|> do Var . show <$> countingNumber

evalT :: [Symbol] -> String -> Either String Term
evalT syms = eval (termP syms)

varsT :: Term -> [Term]
varsT (Var v)     = [Var v]
varsT (ConstT _)  = []
varsT (Func _ ts) = nub $ concatMap varsT ts

subT :: Term -> Term -> Term -> Term
subT t (Var x) (Var y) = if x == y then t else Var y
subT _ _ (ConstT c)    = ConstT c
subT t v (Func f ts)   = Func f (map (subT t v) ts)
subT _ _ t             = t

type Variable = Term

isFree :: Variable -> Bool
isFree (Var x) = all isDigit x
isFree _ = False

{-
  Accepts a set of all recognised
  variables within a scope and
  returns the next free variable
-}
newFreeVar :: [Variable] -> Term
newFreeVar vs = Var $ show index
  where index = length (filter isFree vs)
