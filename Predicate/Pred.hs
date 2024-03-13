module Predicate.Pred(
  Pred(..),
  l1P,
  evalF,
  vars,
  freeVars,
  boundVars,
  sub
) where

import Predicate.Symbol
import Parser
import Predicate.Term
import Control.Applicative hiding (Const)
import Data.List
import Utils

data Pred = Const Bool
          | Eql  Term Term
          | Rel  String [Term]
          | Not  Pred
          | And  Pred   Pred
          | Or   Pred   Pred
          | Imp  Pred   Pred
          | Equi Pred   Pred
          | All  String Pred
          | Exi  String Pred

instance Show Pred where
  show :: Pred -> String
  show (Const x)    = if x then "T" else "F"
  show (x `Eql` y)  = "(" ++ show x ++ " = " ++ show y ++ ")"
  show (Rel x xs)   =   x ++ prettyArgs xs
  show (Not p)      = "¬" ++ show p
  show (p `And` q)  = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
  show (p `Or` q)   = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
  show (p `Imp` q)  = "(" ++ show p ++ " → " ++ show q ++ ")"
  show (p `Equi` q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")"
  show (All v p)    = "∀" ++ v ++ "." ++ show p
  show (Exi v p)    = "∃" ++ v ++ "." ++ show p

instance Eq Pred where
  (==) :: Pred -> Pred -> Bool
  (Const x)    == (Const y)    =  x == y
  (u `Eql` v)  == (x `Eql` y)  = (u == x && v == y) || (u == y && v == x)
  (Rel x xs)   == (Rel y ys)   =  x == y && xs == ys
  (Not p)      == (Not q)      =  p == q
  (p `And` q)  == (r `And` s)  = (p == r && q == s) || (p == s && q == r)
  (p `Or` q)   == (r `Or` s)   = (p == r && q == s) || (p == s && q == r)
  (p `Imp` q)  == (r `Imp` s)  =  p == r && q == s
  (p `Equi` q) == (r `Equi` s) = (p == r && q == s) || (p == s && q == r)
  (All v p)    == (All u q)    =  v == u && p == q
  (Exi v p)    == (Exi u q)    =  v == u && p == q
  _            == _            =  False

l1P :: [Symbol] -> Parser Pred
l1P syms = l2P syms >>= \p ->
             do symbol "<->" <|> symbol "↔"
                q <- l1P syms
                return $ p `Equi` q
            <|> return p

l2P :: [Symbol] -> Parser Pred
l2P syms = l3P syms >>= \p ->
             do symbol "->" <|> symbol "→"
                q <- l2P syms
                return $ p `Imp` q
            <|> return p

l3P :: [Symbol] -> Parser Pred
l3P syms = l4P syms >>= \p ->
  do op <- symbol "AND" <|> symbol "∧" <|> symbol "OR" <|> symbol "∨"
     q <- l3P syms
     case op of
       "AND" -> return (p `And` q)
       "∧"   -> return (p `And` q)
       "OR"  -> return (p `Or`  q)
       "∨"   -> return (p `Or`  q)
 <|> return p

-- TODO: Case where there are two of the same
-- quantifier with the same variable e.g. ALL x ALL x(P(x))
-- Reduce to a single quantifier?
l4P :: [Symbol] -> Parser Pred
l4P syms = do symbol "NOT" <|> symbol "¬"
              Not <$> l4P syms
          <|> do symbol "ALL" <|> symbol "∀"
                 v <- lowerStr
                 case getSym v syms of
                      Nothing -> All v <$> l4P syms -- Checking that provided v is not a defined const
                      _       -> empty
          <|> do symbol "EXISTS" <|> symbol "∃"
                 v <- lowerStr
                 case getSym v syms of
                      Nothing -> Exi v <$> l4P syms
                      _       -> empty
          <|> l5P syms

l5P :: [Symbol] -> Parser Pred
l5P syms = do symbol "T" <|> symbol "TRUE"
              return $ Const True
      <|> do symbol "F" <|> symbol "FALSE"
             return $ Const False
      <|> do r <- upperStartStr
             case getSym r syms of
                  Just (Relation _ arity) -> do symbol "("
                                                ts <- listN arity $ termP syms
                                                symbol ")"
                                                return $ Rel r ts
                  _                       -> empty
      <|> do symbol "("
             p <- l1P syms
             symbol ")"
             return p
      <|> do l <- termP syms
             symbol "="
             r <- termP syms
             return $ l `Eql` r

evalF :: [Symbol] -> String -> Either String Pred
evalF syms = eval (l1P syms)

vars :: Pred -> [Term]
vars (Const _) = []
vars (x `Eql` y)  = varsT x ++ varsT y
vars (Rel _ xs)   = nub $ concatMap varsT xs
vars (Not p)      = vars p
vars (p `And` q)  = vars p ++ vars q
vars (p `Or` q)   = vars p ++ vars q
vars (p `Imp` q)  = vars p ++ vars q
vars (p `Equi` q) = vars p ++ vars q
vars (All _ p)    = vars p
vars (Exi _ p)    = vars p

freeVars :: Pred -> [Term]
freeVars (Const _)    = []
freeVars (x `Eql` y)  = varsT x ++ varsT y
freeVars (Rel _ xs)   = concatMap varsT xs
freeVars (Not p)      = freeVars p
freeVars (p `And` q)  = freeVars p ++ freeVars q
freeVars (p `Or` q)   = freeVars p ++ freeVars q
freeVars (p `Imp` q)  = freeVars p ++ freeVars q
freeVars (p `Equi` q) = freeVars p ++ freeVars q
freeVars (All v p)    = filter (/= Var v) (freeVars p)
freeVars (Exi v p)    = filter (/= Var v) (freeVars p)

boundVars :: Pred -> [Term]
boundVars (Const _)    = []
boundVars (x `Eql` y)  = []
boundVars (Rel _ _)    = []
boundVars (Not p)      = boundVars p
boundVars (p `And` q)  = boundVars p ++ boundVars q
boundVars (p `Or` q)   = boundVars p ++ boundVars q
boundVars (p `Imp` q)  = boundVars p ++ boundVars q
boundVars (p `Equi` q) = boundVars p ++ boundVars q
boundVars (All v p)    = boundVars p ++ filter (== Var v) (freeVars p)
boundVars (Exi v p)    = boundVars p ++ filter (== Var v) (freeVars p)

sub :: Term -> Term -> Pred -> Pred
sub _ _ (Const x) = Const x
sub t v (x `Eql` y)  = subT t v x `Eql` subT t v x
sub t v (Rel x xs)   = Rel x (map (subT t v) xs)
sub t v (Not p)      = Not (sub t v p)
sub t v (p `And` q)  = sub t v p `And` sub t v q
sub t v (p `Or` q)   = sub t v p `Or` sub t v q
sub t v (p `Imp` q)  = sub t v p `Imp` sub t v q
sub t v (p `Equi` q) = sub t v p `Equi` sub t v q
sub t v (All x p)    = if v == Var x then All x p else All x (sub t v p)
sub t v (Exi x p)    = if v == Var x then Exi x p else Exi x (sub t v p)