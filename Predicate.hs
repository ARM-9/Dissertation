{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Predicate(
    Pred(..),
    Term(..),
) where

import Data.List (intercalate)
import Control.Applicative hiding (Const)
import Parser
import Sequent

data Pred = Const Bool
          | Eql Term Term
          | Rel Char [Term]
          | Not     Pred
          | And     Pred Pred
          | Or      Pred Pred
          | Imp Pred Pred
          | Equi Pred Pred
          | All  Char Pred
          | Exi  Char Pred
          deriving (Read, Eq)

instance Show Pred where
  show :: Pred -> String
  show (Const x) = if x then "T" else "F"
  show (x `Eql` y) = "(" ++ show x ++ " = " ++ show y ++ ")"
  show (Rel x ys) = x : arguments ys
  show (Not x) = "¬" ++ show x
  show (x `And` y) = "(" ++ show x ++ " ∧ " ++ show y ++ ")"
  show (x `Or` y)  = "(" ++ show x ++ " ∨ " ++ show y ++ ")"
  show (x `Imp` y) = "(" ++ show x ++ " → " ++ show y ++ ")"
  show (x `Equi` y) = "(" ++ show x ++ " ↔ " ++ show y ++ ")"
  show (x `All` y) = "∀" ++ [x] ++ "." ++ show y
  show (Exi x y) = "∃" ++ [x] ++ "." ++ show y

data Term = Var Char
          | Func Char [Term]
          deriving (Read, Eq)

instance Show Term where
  show :: Term -> String
  show (Var x) = [x]
  show (Func f xs) = f : arguments xs

arguments :: Show t => [t] -> String
arguments [] = ""
arguments ts = "(" ++ intercalate ", " (map show ts) ++ ")"

l1P :: Parser Pred
l1P = do l <- l2P
         do symbol "<->" <|> symbol "↔"
            r <- l1P
            return (l `Equi` r)
          <|> return l

l2P :: Parser Pred
l2P = do l <- l3P
         do symbol "->" <|> symbol "→"
            r <- l2P
            return (l `Imp` r)
          <|> return l

l3P :: Parser Pred
l3P = do l <- l4P
         do symbol "AND" <|> symbol "∧"
            r <- l3P
            return (l `And` r)
          <|> do symbol "OR" <|> symbol "∨"
                 r <- l3P
                 return (l `Or` r)
          <|> return l

l4P :: Parser Pred
l4P = do symbol "NOT" <|> symbol "¬"
         Not <$> l4P
      <|> do symbol "ALL" <|> symbol "∀"
             v <- lower
             All v <$> l4P
      <|> do symbol "EXISTS" <|> symbol "∃"
             v <- lower
             Exi v <$> l4P
      <|> l5P

l5P :: Parser Pred
l5P = do s <- upper
         symbol "("
         ts <- list term
         symbol ")"
         return $ Rel s ts
      <|> do symbol "T" <|> symbol "TRUE"
             return $ Const True
      <|> do symbol "F" <|> symbol "FALSE"
             return $ Const False
      <|> do symbol "("
             p <- l1P
             symbol ")"
             return p
      <|> do l <- term
             symbol "="
             r <- term
             return $ l `Eql` r

term :: Parser Term
term = do s <- lower
          symbol "("
          ts <- list term
          symbol ")"
          return $ Func s ts
      <|> Var <$> lower

evalF :: String -> Either String Pred
evalF = eval l1P

sequentP :: Parser (Sequent Pred)
sequentP = do l <- l1P
              do symbol "|-" <|> symbol "⊢"
                 r <- l1P
                 return ([l] `Entails` r)
               <|> do symbol "-||-" <|> symbol "⟛"
                      r <- l1P
                      return (l `Biconditional` r)
             <|> do ls <- list l1P
                    symbol "|-" <|> symbol "⊢"
                    r <- l1P
                    return (ls `Entails` r)
             <|> do symbol "|-" <|> symbol "⊢"
                    r <- l1P
                    return ([] `Entails` r)

evalS :: String -> Either String (Sequent Pred)
evalS = eval sequentP