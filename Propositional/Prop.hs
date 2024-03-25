module Propositional.Prop(
  Prop(..),
  propP,
  evalP
) where

import Parser
import Control.Applicative hiding (Const)

data Prop = Const Bool
          | Var   String
          | Not   Prop
          | And   Prop Prop
          | Or    Prop Prop
          | Imp   Prop Prop
          | Bicon Prop Prop
          deriving (Read)

instance Show Prop where
  show :: Prop -> String
  show (Const x)     = if x then "T" else "F"
  show (Var x)       = x
  show (Not p)       = "¬" ++ show p
  show (p `And` q)   = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
  show (p `Or` q)    = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
  show (p `Imp` q)   = "(" ++ show p ++ " → " ++ show q ++ ")"
  show (p `Bicon` q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")"

instance Eq Prop where
  (==) :: Prop -> Prop -> Bool
  (Const x)     == (Const y)   =  x == y
  (Var x)       == (Var y)     =  x == y
  (Not p)       == (Not q)     =  p == q
  (p `And` q)   == (r `And` s) = (p == r && q == s) || (p == s && q == r)
  (p `Or` q)    == (r `Or` s)  = (p == r && q == s) || (p == s && q == r)
  (p `Imp` q)   == (r `Imp` s) =  p == r && q == s
  (p `Bicon` q) == (r `Or` s)  = (p == r && q == s) || (p == s && q == r)
  _             == _           =  False

propP :: Parser Prop
propP = l1P

l1P :: Parser Prop
l1P = l2P >>= \p ->
        do symbol "<->" <|> symbol "↔"
           q <- l1P
           return $ p `Bicon` q
       <|> return p

l2P :: Parser Prop
l2P = l3P >>= \p ->
        do symbol "->" <|> symbol "→"
           q <- l2P
           return $ p `Imp` q
       <|> return p

l3P :: Parser Prop
l3P = l4P >>= \l ->
  do op <- symbol "AND" <|> symbol "∧" <|> symbol "OR" <|> symbol "∨"
     r <- l3P
     case op of
       "AND" -> return (l `And` r)
       "∧"   -> return (l `And` r)
       "OR"  -> return (l `Or` r)
       "∨"   -> return (l `Or` r)
 <|> return l

l4P :: Parser Prop
l4P = do symbol "NOT" <|> symbol "¬" >> Not <$> l4P
      <|> l5P

l5P :: Parser Prop
l5P = do symbol "("
         l <- l1P
         symbol ")"
         return l
      <|> (symbol "T" >> return (Const True))
      <|> (symbol "F" >> return (Const False))
      <|> Var <$> lowerStr

evalP :: String -> Either String Prop
evalP = eval l1P