{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Use lambda-case" #-}

{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

module Propositional(
  Prop(..),
  main
) where

import Control.Applicative hiding (Const)
import Parser
import Sequent
import Data.Either
import System.Console.Haskeline
import System.IO
import Debug.Trace

data Prop = Const   Bool
          | Var     Char
          | Not     Prop
          | And     Prop Prop
          | Or      Prop Prop
          | Imp     Prop Prop
          | Equi    Prop Prop
          deriving (Read)

instance Show Prop where
  show :: Prop -> String
  show (Const x)    = if x then "T" else "F"
  show (Var x)      = [x]
  show (Not x)      = "¬" ++ show x
  show (x `And` y)  = "(" ++ show x ++ " ∧ " ++ show y ++ ")"
  show (x `Or` y)   = "(" ++ show x ++ " ∨ " ++ show y ++ ")"
  show (x `Imp` y)  = "(" ++ show x ++ " → " ++ show y ++ ")"
  show (x `Equi` y) = "(" ++ show x ++ " ↔ " ++ show y ++ ")"

instance Eq Prop where
  (==) :: Prop -> Prop -> Bool
  (Const x)    == (Const y)    =  x == y
  (Var x)      == (Var y)      =  x == y
  (Not p)      == (Not q)      =  p == q
  (p `And` q)  == (r `And` s)  = (p == r && q == s) || (p == s && q == r)
  (p `Or` q)   == (r `Or` s)   = (p == r && q == s) || (p == s && q == r)
  (p `Imp` q)  == (r `Imp` s)  =  p == r && q == s
  (p `Equi` q) == (r `Equi` s) = (p == r && q == s) || (p == s && q == r)
  _            == _            = False

l1P :: Parser Prop
l1P = l2P >>= \l ->
        do symbol "<->" <|> symbol "↔"
           r <- l1P
           return $ l `Equi` r
       <|> return l

l2P :: Parser Prop
l2P = l3P >>= \l ->
        do symbol "->" <|> symbol "→"
           r <- l2P
           return $ l `Imp` r
       <|> return l

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
      <|> Var <$> lower

evalF :: String -> Either String Prop
evalF = eval l1P

sequentP :: Parser (Sequent Prop)
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

evalS :: String -> Either String (Sequent Prop)
evalS = eval sequentP

-- LOGIC ENGINE PROTOTYPING

data Rule = EmptyRule
          | AndIntro   Prop Prop
          | AndElimL   Prop
          | AndElimR   Prop
          | ImpIntro -- (Sequent Prop) -- xx
          | ImpElim    Prop Prop
          | OrIntroL   Prop Prop
          | OrIntroR   Prop Prop
          | OrELim     Prop Prop -- (Sequent Prop) (Sequent Prop) -- xx
          | NotIntro -- (Sequent Prop) -- xx
          | NotELim    Prop Prop
          | TopIntro
          | BottomElim Prop
          | StmtIntro  Prop
          | Pbc -- (Sequent Prop) -- xx
          deriving (Show, Read)

ruleP :: Parser Rule
ruleP = do (p, q) <- binaryRuleP "ANDI"
           return $ AndIntro p q
       <|> do p <- unaryRuleP "ANDEl"
              return $ AndElimL p
       <|> do p <- unaryRuleP "ANDEr"
              return $ AndElimR p
       <|> do symbol "IMPI"
              return ImpIntro
       <|> do (p, q) <- binaryRuleP "IMPE"
              return $ ImpElim p q
       <|> do (p, q) <- binaryRuleP "ORIl"
              return $ OrIntroL p q
       <|> do (p, q) <- binaryRuleP "ORIr"
              return $ OrIntroR p q
       <|> do (p, q) <- binaryRuleP "ORE"
              return $ OrELim p q
       <|> do symbol "NOTI"
              return NotIntro
       <|> do (p, q) <- binaryRuleP "NOTE"
              return $ NotELim p q
       <|> do symbol "TOPI"
              return TopIntro
       <|> do p <- unaryRuleP "BOTE"
              return $ BottomElim p
       <|> do p <- unaryRuleP "STMTI"
              return $ StmtIntro p
       <|> do p <- symbol "PBC"
              return Pbc

unaryRuleP :: String -> Parser Prop
unaryRuleP rule = do symbol rule
                     comma
                     l1P

binaryRuleP :: String -> Parser (Prop, Prop)
binaryRuleP rule = do symbol rule
                      comma
                      p <- l1P
                      comma
                      q <- l1P
                      return (p, q)

evalR :: String -> Either String Rule
evalR = eval ruleP

data ProofTree p = Leaf (Sequent p)
                 | ApplyRule Rule (Sequent p) (ProofTree p)
                 | OpenSubproof Rule (Sequent p) (ProofTree p)
                 | BranchProof Rule (Sequent p) (ProofTree p) (ProofTree p)

data RuleApplication p = ErroneousApplication String
                       | SingleApplication (Sequent p)
                       | BranchingApplication (Sequent p) (Sequent p)

setInsert :: Eq a => [a] -> a -> [a]
setInsert xs x = if x `elem` xs then xs else xs ++ [x]

errorBicond :: RuleApplication Prop
errorBicond = ErroneousApplication "Function undefined for biconditionals"

andI :: Sequent Prop -> Prop -> Prop -> RuleApplication Prop
andI (as `Entails` c) p q
    | p `elem` as && q `elem` as = SingleApplication (setInsert as (p `And` q) `Entails` c)
    | otherwise = ErroneousApplication "One or both propositions are not in scope"
andI _ _ _ = errorBicond

andEl :: Sequent Prop -> Prop -> RuleApplication Prop
andEl (as `Entails` c) (p `And` q)
    | (p `And` q) `elem` as = SingleApplication (setInsert as p `Entails` c)
    | otherwise = ErroneousApplication "andEl: AND proposition not in scope"
andEl _ (_ `And` _) = errorBicond
andEl _ _ = ErroneousApplication "andEl: AND proposition must be provided"

andEr :: Sequent Prop -> Prop -> RuleApplication Prop
andEr (as `Entails` c) (p `And` q)
    | (p `And` q) `elem` as = SingleApplication (setInsert as q `Entails` c)
    | otherwise = ErroneousApplication "andEr: AND proposition not in scope"
andEr _ (_ `And` _) = errorBicond
andEr _ _ = ErroneousApplication "andEr: AND proposition must be provided"

impI :: Sequent Prop -> RuleApplication Prop
impI (as `Entails` (p `Imp` q)) = SingleApplication ((p : as) `Entails` q)
impI (_ `Entails` _) = ErroneousApplication "impI: Consequent must be an IMPLICATION"
impI _ = errorBicond

impE :: Sequent Prop -> Prop -> Prop -> RuleApplication Prop
impE (as `Entails` c) (p `Imp` q) r
    | p == r = SingleApplication (setInsert as q `Entails` c)
    | otherwise = ErroneousApplication "impE: Premise does not match provided proposition"
impE (as `Entails` c) r (p `Imp` q)
    | p == r = SingleApplication (setInsert as q `Entails` c)
    | otherwise = ErroneousApplication "impE: Premise does not match provided proposition"
impE (_ `Entails` _) _ _ = ErroneousApplication "impE: IMPLICATION proposition must be provided"
impE _ _ _ = errorBicond

orIl :: Sequent Prop -> Prop -> Prop -> RuleApplication Prop
orIl (as `Entails` c) p q
    | p `elem` as = SingleApplication (setInsert as (p `Or` q) `Entails` c)
    | otherwise = ErroneousApplication "orIl: Proposition not in scope"
orIl _ _ _ = errorBicond

orIr :: Sequent Prop -> Prop -> Prop -> RuleApplication Prop
orIr (as `Entails` c) p q
    | p `elem` as = SingleApplication (setInsert as (q `Or` p) `Entails` c)
    | otherwise = ErroneousApplication "orIr: Proposition not in scope"
orIr _ _ _ = errorBicond

orE :: Sequent Prop -> Prop -> Prop -> RuleApplication Prop
orE (as `Entails` _) (p `Or` q) r
    | (p `Or` q) `elem` as = BranchingApplication ((p :as) `Entails` r) ((q : as) `Entails` r)
    | otherwise = ErroneousApplication "orE: Proposition not in scope"
orE (_ `Entails` _) _ _ = ErroneousApplication "orE: OR proposition must be provided"
orE _ _ _ = ErroneousApplication "orE: Function undefined for biconditionals"

notI :: Sequent Prop -> RuleApplication Prop
notI (as `Entails` (Not p)) = SingleApplication ((p : as) `Entails` Const False)
notI (_ `Entails` _) = ErroneousApplication "notI: NOT proposition must be provided"
notI _ = errorBicond

notE :: Sequent Prop -> Prop -> Prop -> RuleApplication Prop
notE (as `Entails` c) p (Not q)
    | p `elem` as && Not q `elem` as && p == q = SingleApplication (setInsert as (Const False) `Entails` c)
    | otherwise = ErroneousApplication "notE: One or both propositions are not in scope"
notE (as `Entails` c) (Not q) p
    | p `elem` as && Not q `elem` as && p == q = SingleApplication (setInsert as (Const False) `Entails` c)
    | otherwise = ErroneousApplication "notE: One or both propositions are not in scope"
notE _ _ _ = errorBicond

topI :: Sequent Prop -> RuleApplication Prop
topI (as `Entails` c) = SingleApplication (setInsert as (Const True) `Entails` c)
topI _ = errorBicond

botE :: Sequent Prop -> Prop -> RuleApplication Prop
botE (as `Entails` c) p
    | Const False `elem` as = SingleApplication (setInsert as p `Entails` c)
    | otherwise = ErroneousApplication "botE: BOTTOM proposition not in scope"
botE _ _ = errorBicond

stmtI :: Sequent Prop -> Prop -> RuleApplication Prop
stmtI (as `Entails` c) p = BranchingApplication (as `Entails` p) (setInsert as p `Entails` c)
stmtI _ _ = errorBicond

pbc :: Sequent Prop -> RuleApplication Prop
pbc (as `Entails` c) = SingleApplication ((Not c : as) `Entails` Const False)
pbc _ = errorBicond

applyRule :: Sequent Prop -> Rule -> RuleApplication Prop
applyRule s rule = case rule of
       (AndIntro p q) -> andI  s p q
       (AndElimL p)   -> andEl s p
       (AndElimR p)   -> andEr s p
       ImpIntro       -> impI  s
       (ImpElim p q)  -> impE  s p q
       (OrIntroL p q) -> orIl  s p q
       (OrIntroR p q) -> orIr  s p q
       (OrELim p q)   -> orE   s p q
       NotIntro       -> notI  s
       (NotELim p q)  -> notE  s p q
       TopIntro       -> topI  s
       (BottomElim p) -> botE  s p
       (StmtIntro p)  -> stmtI s p
       Pbc            -> pbc   s

applyRule' :: Sequent Prop -> IO Bool
applyRule' s = do
  print s
  r <- getRule "Enter a rule: "
  let ruleApl = applyRule s r
  case ruleApl of
    ErroneousApplication str -> do
      putStrLn $ "Error: " ++ str
      applyRule' s
    SingleApplication s1 -> do
       applyRule'' s1
    BranchingApplication s1 s2 -> do
       result1 <- applyRule'' s1
       result2 <- applyRule'' s2
       return $ result1 && result2

applyRule'' :: Sequent Prop -> IO Bool
applyRule'' s = do if solved s then return True else applyRule' s

getRule :: String -> IO Rule
getRule text = do
  input <- prompt text
  case evalR input of
    Right rule -> return rule
    Left errMsg -> do
      putStrLn errMsg
      getRule text

-- Inititially included BOTTOM
solved :: Sequent Prop -> Bool
solved (as `Entails` c) = c `elem` as

prompt :: String -> IO String
prompt text = runInputT defaultSettings $ do
  getInputLine text >>= \case
    Nothing   -> return ""
    Just line -> return line

getSequent :: String -> IO (Sequent Prop)
getSequent p = do xs <- prompt p
                  let s = evalS xs
                  case s of
                    (Right s) -> return s
                    (Left errMsg) -> getSequent p

runEngine :: IO Bool
runEngine = do s <- getSequent "Input a sequent: "
               case s of
                 (_ `Entails` _) -> applyRule'' s
                 (a `Biconditional` c) -> do
                   res1 <- applyRule'' ([a] `Entails` c)
                   res2 <- applyRule'' ([c] `Entails` a)
                   return $ res1 && res2

main :: IO ()
main = do r <- runEngine
          print r
          return ()
