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
import Data.Maybe

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
          | ConstT Char
          | Func Char [Term]
          deriving (Read, Eq)

instance Show Term where
  show :: Term -> String
  show (Var x) = [x]
  show (ConstT x) = [x]
  show (Func f xs) = f : arguments xs

arguments :: Show t => [t] -> String
arguments [] = ""
arguments ts = "(" ++ intercalate ", " (map show ts) ++ ")"

l1P :: [Symbol] -> Parser Pred
l1P syms = do l <- l2P syms
              do symbol "<->" <|> symbol "↔"
                 r <- l1P syms
                 return (l `Equi` r)
               <|> return l

l2P :: [Symbol] -> Parser Pred
l2P syms = do l <- l3P syms
              do symbol "->" <|> symbol "→"
                 r <- l2P syms
                 return (l `Imp` r)
               <|> return l

l3P :: [Symbol] -> Parser Pred
l3P syms = do l <- l4P syms
              do symbol "AND" <|> symbol "∧"
                 r <- l3P syms
                 return (l `And` r)
               <|> do symbol "OR" <|> symbol "∨"
                      r <- l3P syms
                      return (l `Or` r)
               <|> return l

-- TODO: Case where there are two of the same
-- quantifier with the same variable e.g. ALL x ALL x(P(x))
-- Reduce to a single quantifier?
l4P :: [Symbol] -> Parser Pred
l4P syms = do symbol "NOT" <|> symbol "¬"
              Not <$> l4P syms
           <|> do symbol "ALL" <|> symbol "∀"
                  v <- lower
                  let arity = getArity v syms
                  if isJust arity then
                     empty
                  else All v <$> l4P syms
           <|> do symbol "EXISTS" <|> symbol "∃"
                  v <- lower
                  let arity = getArity v syms
                  if isJust arity then
                     empty
                  else Exi v <$> l4P syms
           <|> l5P syms

l5P :: [Symbol] -> Parser Pred
l5P syms = do s <- upper
              let arity = getArity s syms
              if isNothing arity then
                 empty
              else do symbol "("
                      ts <- listN (fromJust arity) $ term syms
                      symbol ")"
                      return $ Rel s ts
      <|> do symbol "T" <|> symbol "TRUE"
             return $ Const True
      <|> do symbol "F" <|> symbol "FALSE"
             return $ Const False
      <|> do symbol "("
             p <- l1P syms
             symbol ")"
             return p
      <|> do l <- term []
             symbol "="
             r <- term []
             return $ l `Eql` r

term :: [Symbol] -> Parser Term
term syms = do s <- lower
               let arity = getArity s syms
               if isNothing arity then
                  empty
               else do symbol "("
                       ts <- listN (fromJust arity) (term syms)
                       symbol ")"
                       return $ Func s ts
      <|> do x <- lower
             let arity = getArity x syms
             if isNothing arity then
                return $ Var x
             else if fromJust arity == 0 then
                     return $ ConstT x
             else
                empty

evalF :: [Symbol] -> String -> Either String Pred
evalF syms = eval (l1P syms)

sequentP :: [Symbol] -> Parser (Sequent Pred)
sequentP syms = do l <- l1P syms
                   do symbol "|-" <|> symbol "⊢"
                      r <- l1P syms
                      return ([l] `Entails` r)
                    <|> do symbol "-||-" <|> symbol "⟛"
                           r <- l1P syms
                           return (l `Biconditional` r)
                <|> do ls <- list $ l1P syms
                       symbol "|-" <|> symbol "⊢"
                       r <- l1P syms
                       return (ls `Entails` r)
                <|> do symbol "|-" <|> symbol "⊢"
                       r <- l1P syms
                       return ([] `Entails` r)

evalS :: [Symbol] -> String -> Either String (Sequent Pred)
evalS syms = eval (sequentP syms)

data Symbol = Constant Char
            | Function Char Int
            | Relation Char Int
            deriving (Show, Read, Eq)

arityP :: Parser Int
arityP = do symbol "("
            n <- number
            symbol ")"
            return n

symP :: [Symbol] -> Parser Symbol
symP syms = do r <- upper
               if isJust $ getArity r syms
                  then empty
               else do n <- arityP
                       let rel = Relation r n
                       if rel `elem` syms then
                          empty
                       else
                          return rel
            <|> do f <- lower
                   if isJust $ getArity f syms
                      then empty
                   else do n <- arityP
                           let func = Function f n
                           if func `elem` syms then
                              empty
                           else
                              return func
            <|> do c <- lower
                   if isJust $ getArity c syms
                      then empty
                   else do let const = Constant c
                           if const `elem` syms then
                              empty
                           else
                              return const

symsP :: [Symbol] -> Parser [Symbol]
symsP syms = do sym <- symP syms
                do comma
                   others <- symsP (sym:syms)
                   return (sym:others)
                 <|> return [sym]

getArity :: Char -> [Symbol] -> Maybe Int
getArity _ [] = Nothing
getArity c ((Constant sym):syms) = if c == sym then Just 0 else getArity c syms
getArity c ((Function sym arity):syms) = if c == sym then Just arity else getArity c syms
getArity c ((Relation sym arity):syms) = if c == sym then Just arity else getArity c syms

