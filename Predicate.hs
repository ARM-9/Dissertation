{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

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
import System.Console.Haskeline

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
  show (All x y) = "∀" ++ [x] ++ "." ++ show y
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

rmDupes :: Eq a => [a] -> [a]
rmDupes [] = []
rmDupes (x:xs) = if x `elem` xs then rmDupes xs else x : rmDupes xs

vars :: Pred -> [Term]
vars (Const _) = []
vars (x `Eql` y) = varsT x ++ varsT y
vars (Rel _ ts) = concatMap varsT ts
vars (Not p) = vars p
vars (p `And` q) = vars p ++ vars q
vars (p `Or` q) = vars p ++ vars q
vars (p `Imp` q) = vars p ++ vars q
vars (p `Equi` q) = vars p ++ vars q
vars (All _ p) = vars p
vars (Exi _ p) = vars p

varsT :: Term -> [Term]
varsT (Var v) = [Var v]
varsT (ConstT _) = []
varsT (Func _ ts) = concatMap varsT ts

freeVars :: Pred -> [Term]
freeVars (Const _) = []
freeVars (x `Eql` y) = varsT x ++ varsT y
freeVars (Rel _ ts) = concatMap varsT ts
freeVars (Not p) = freeVars p
freeVars (p `And` q) = freeVars p ++ freeVars q
freeVars (p `Or` q) = freeVars p ++ freeVars q
freeVars (p `Imp` q) = freeVars p ++ freeVars q
freeVars (p `Equi` q) = freeVars p ++ freeVars q
freeVars (All v p) = filter (/= Var v) (freeVars p)
freeVars (Exi v p) = filter (/= Var v) (freeVars p)

boundVars :: Pred -> [Term]
boundVars (Const _) = []
boundVars (x `Eql` y) = []
boundVars (Rel _ _) = []
boundVars (Not p) = boundVars p
boundVars (p `And` q) = boundVars p ++ boundVars q
boundVars (p `Or` q) = boundVars p ++ boundVars q
boundVars (p `Imp` q) = boundVars p ++ boundVars q
boundVars (p `Equi` q) = boundVars p ++ boundVars q
boundVars (All v p) = boundVars p ++ filter (== Var v) (freeVars p)
boundVars (Exi v p) = boundVars p ++ filter (== Var v) (freeVars p)

sub :: Term -> Term -> Pred -> Pred
sub _ _ (Const x) = Const x
sub t v (x `Eql` y) = subT t v x `Eql` subT t v x
sub t v (Rel x ts) = Rel x (map (subT t v) ts)
sub t v (Not p) = Not (sub t v p)
sub t v (p `And` q) = sub t v p `And` sub t v q
sub t v (p `Or` q) = sub t v p `And` sub t v q
sub t v (p `Imp` q) = sub t v p `And` sub t v q
sub t v (p `Equi` q) = sub t v p `And` sub t v q
sub t v (All x p) = if v == Var x then All x p else All x (sub t v p)
sub t v (Exi x p) = if v == Var x then All x p else All x (sub t v p)

subT :: Term -> Term -> Term -> Term
subT t (Var x) (Var y) = if x == y then t else Var y
subT _ _ (ConstT c) = ConstT c
subT t v (Func f ts) = Func f (map (subT t v) ts)

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
                  let arity = getArity v syms -- TODO: Make isConst function to increase clarity
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
      <|> do l <- term syms
             symbol "="
             r <- term syms
             return $ l `Eql` r

evalF :: [Symbol] -> String -> Either String Pred
evalF syms = eval (l1P syms)

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

evalT :: [Symbol] -> String -> Either String Term
evalT syms = eval (term syms)

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
            deriving (Read)

instance Show Symbol where
   show :: Symbol -> String
   show (Constant c) = [c]
   show (Function f n) = f : "(" ++ show n ++ ")"
   show (Relation r n) = r : "(" ++ show n ++ ")"

arityP :: Parser Int
arityP = do symbol "("
            n <- number
            symbol ")"
            return n

symP :: [Symbol] -> Parser Symbol
symP syms = do r <- upper
               if isJust $ getArity r syms
                  then empty
               else Relation r <$> arityP
            <|> do f <- lower
                   if isJust $ getArity f syms
                      then empty
                   else Function f <$> arityP
            <|> do c <- lower
                   if isJust $ getArity c syms
                      then empty
                   else return $ Constant c

symsP :: [Symbol] -> Parser [Symbol]
symsP syms = do sym <- symP syms
                do comma
                   others <- symsP (sym:syms)
                   return (sym:others)
                 <|> return [sym]
             <|> do symbol "-"
                    return []

evalSyms :: String -> Either String [Symbol]
evalSyms = eval (symsP [])

getArity :: Char -> [Symbol] -> Maybe Int
getArity _ [] = Nothing
getArity c ((Constant sym):syms) = if c == sym then Just 0 else getArity c syms
getArity c ((Function sym arity):syms) = if c == sym then Just arity else getArity c syms
getArity c ((Relation sym arity):syms) = if c == sym then Just arity else getArity c syms

data Rule = EmptyRule
          | AndIntro   Pred Pred
          | AndElimL   Pred
          | AndElimR   Pred
          | ImpIntro -- (Sequent Pred) -- xx
          | ImpElim    Pred Pred
          | OrIntroL   Pred Pred
          | OrIntroR   Pred Pred
          | OrELim     Pred -- (Sequent Pred) (Sequent Pred) -- xx
          | NotIntro -- (Sequent Pred) -- xx
          | NotELim    Pred Pred
          | TopIntro
          | BottomElim Pred
          | StmtIntro  Pred
          | Pbc -- (Sequent Pred) -- xx
          deriving (Show, Read)

ruleP :: [Symbol] -> Parser Rule
ruleP syms = do (p, q) <- binaryRuleP syms "ANDI"
                return $ AndIntro p q
             <|> do p <- unaryRuleP syms "ANDEl"
                    return $ AndElimL p
             <|> do p <- unaryRuleP syms "ANDEr"
                    return $ AndElimR p
             <|> do symbol "IMPI"
                    return ImpIntro
             <|> do (p, q) <- binaryRuleP syms "IMPE"
                    return $ ImpElim p q
             <|> do (p, q) <- binaryRuleP syms "ORIl"
                    return $ OrIntroL p q
             <|> do (p, q) <- binaryRuleP syms "ORIr"
                    return $ OrIntroR p q
             <|> do p <- unaryRuleP syms "ORE"
                    return $ OrELim p
             <|> do symbol "NOTI"
                    return NotIntro
             <|> do (p, q) <- binaryRuleP syms "NOTE"
                    return $ NotELim p q
             <|> do symbol "TOPI"
                    return TopIntro
             <|> do p <- unaryRuleP syms "BOTE"
                    return $ BottomElim p
             <|> do p <- unaryRuleP syms "STMTI"
                    return $ StmtIntro p
             <|> do p <- symbol "PBC"
                    return Pbc

unaryRuleP :: [Symbol] -> String -> Parser Pred
unaryRuleP syms rule = do symbol rule
                          comma
                          l1P syms

binaryRuleP :: [Symbol] -> String -> Parser (Pred, Pred)
binaryRuleP syms rule = do symbol rule
                           comma
                           p <- l1P syms
                           comma
                           q <- l1P syms
                           return (p, q)

evalR :: [Symbol] -> String -> Either String Rule
evalR syms = eval (ruleP syms)

data RuleApplication p = ErroneousApplication String
                       | SingleApplication (Sequent p)
                       | BranchingApplication (Sequent p) (Sequent p)

setInsert :: Eq a => [a] -> a -> [a]
setInsert xs x = if x `elem` xs then xs else xs ++ [x]

errorBicond :: RuleApplication Pred
errorBicond = ErroneousApplication "Function undefined for biconditionals"

andI :: Sequent Pred -> Pred -> Pred -> RuleApplication Pred
andI (as `Entails` c) p q
    | p `elem` as && q `elem` as = SingleApplication (setInsert as (p `And` q) `Entails` c)
    | otherwise = ErroneousApplication "One or both propositions are not in scope"
andI _ _ _ = errorBicond

andEl :: Sequent Pred -> Pred -> RuleApplication Pred
andEl (as `Entails` c) (p `And` q)
    | (p `And` q) `elem` as = SingleApplication (setInsert as p `Entails` c)
    | otherwise = ErroneousApplication "Predosition not in scope"
andEl (_ `Entails` _) _ = ErroneousApplication "Conjunctive proposition must be provided"
andEl _ _ = errorBicond

andEr :: Sequent Pred -> Pred -> RuleApplication Pred
andEr s (p `And` q) = andEl s (q `And` p)

impI :: Sequent Pred -> RuleApplication Pred
impI (as `Entails` (p `Imp` q)) = SingleApplication ((p : as) `Entails` q)
impI (_ `Entails` _) = ErroneousApplication "Consequent must be an implicative proposition"
impI _ = errorBicond

impE :: Sequent Pred -> Pred -> Pred -> RuleApplication Pred
impE (as `Entails` c) (p `Imp` q) r
    | p == r = SingleApplication (setInsert as q `Entails` c)
    | otherwise = ErroneousApplication "Premise of provided implication does not match provided proposition"
impE (as `Entails` c) r (p `Imp` q) = impE (as `Entails` c) (p `Imp` q) r
impE (_ `Entails` _) _ _ = ErroneousApplication "Implication proposition must be provided"
impE _ _ _ = errorBicond

orIl :: Sequent Pred -> Pred -> Pred -> RuleApplication Pred
orIl (as `Entails` c) p q
    | p `elem` as = SingleApplication (setInsert as (p `Or` q) `Entails` c)
    | otherwise = ErroneousApplication "Predosition not in scope"
orIl _ _ _ = errorBicond

orIr :: Sequent Pred -> Pred -> Pred -> RuleApplication Pred
orIr s p q = orIl s q p

orE :: Sequent Pred -> Pred -> RuleApplication Pred
orE (as `Entails` c) (p `Or` q)
    | (p `Or` q) `elem` as = BranchingApplication ((p :as) `Entails` c) ((q : as) `Entails` c)
    | otherwise = ErroneousApplication "Predosition not in scope"
orE (_ `Entails` _) _ = ErroneousApplication "Consequent must be a disjunctive proposition"
orE _ _ = errorBicond

notI :: Sequent Pred -> RuleApplication Pred
notI (as `Entails` (Not p)) = SingleApplication ((p : as) `Entails` Const False)
notI (_ `Entails` _) = ErroneousApplication "Consequent must be a negative proposition"
notI _ = errorBicond

notE :: Sequent Pred -> Pred -> Pred -> RuleApplication Pred
notE (as `Entails` c) p (Not q)
    | p `elem` as && Not q `elem` as && p == q = SingleApplication (setInsert as (Const False) `Entails` c)
    | p /= q = ErroneousApplication "Predositions must be negations of eachother"
    | otherwise = ErroneousApplication "One or both propositions are not in scope"
notE s (Not q) p = notE s p (Not q)
notE _ _ _ = errorBicond

topI :: Sequent Pred -> RuleApplication Pred
topI (as `Entails` c) = SingleApplication (setInsert as (Const True) `Entails` c)
topI _ = errorBicond

botE :: Sequent Pred -> Pred -> RuleApplication Pred
botE (as `Entails` c) p
    | Const False `elem` as = SingleApplication (setInsert as p `Entails` c)
    | otherwise = ErroneousApplication "Bottom proposition not in scope"
botE _ _ = errorBicond

stmtI :: Sequent Pred -> Pred -> RuleApplication Pred
stmtI (as `Entails` c) p = BranchingApplication (as `Entails` p) (setInsert as p `Entails` c)
stmtI _ _ = errorBicond

pbc :: Sequent Pred -> RuleApplication Pred
pbc (as `Entails` c) = SingleApplication ((Not c : as) `Entails` Const False)
pbc _ = errorBicond

applyRule :: Sequent Pred -> Rule -> RuleApplication Pred
applyRule s rule = case rule of
       (AndIntro p q) -> andI  s p q
       (AndElimL p)   -> andEl s p
       (AndElimR p)   -> andEr s p
       ImpIntro       -> impI  s
       (ImpElim p q)  -> impE  s p q
       (OrIntroL p q) -> orIl  s p q
       (OrIntroR p q) -> orIr  s p q
       (OrELim p)     -> orE   s p
       NotIntro       -> notI  s
       (NotELim p q)  -> notE  s p q
       TopIntro       -> topI  s
       (BottomElim p) -> botE  s p
       (StmtIntro p)  -> stmtI s p
       Pbc            -> pbc   s

applyRule' :: [Symbol] -> Sequent Pred -> IO Bool
applyRule' syms s = do
  print s
  r <- getRule syms "Enter a rule: "
  let ruleApl = applyRule s r
  case ruleApl of
    ErroneousApplication str -> do
      putStrLn $ "Error: " ++ str
      applyRule' syms s
    SingleApplication s1 -> do
       applyRule'' syms s1
    BranchingApplication s1 s2 -> do
       result1 <- applyRule'' syms s1
       result2 <- applyRule'' syms s2
       return $ result1 && result2

applyRule'' :: [Symbol] -> Sequent Pred -> IO Bool
applyRule'' syms s = do if solved s then return True else applyRule' syms s

getRule :: [Symbol] -> String -> IO Rule
getRule syms text = do
  input <- prompt text
  case evalR syms input of
    Right rule -> return rule
    Left errMsg -> putStrLn errMsg >> getRule syms text

solved :: Sequent Pred -> Bool
solved (as `Entails` c) = c `elem` as

prompt :: String -> IO String
prompt text = runInputT defaultSettings $ do
  getInputLine text >>= \case
    Nothing   -> return ""
    Just line -> return line

getSequent :: [Symbol] -> String -> IO (Sequent Pred)
getSequent syms p = do xs <- prompt p
                       let s = evalS syms xs
                       case s of
                         (Right s) -> return s
                         (Left errMsg) -> putStrLn errMsg >> getSequent syms p

getPred :: [Symbol] -> String -> IO Pred
getPred syms p = do xs <- prompt p
                    let s = evalF syms xs
                    case s of
                       (Right s) -> return s
                       (Left errMsg) -> putStrLn errMsg >> getPred syms p

getTerm :: [Symbol] -> String -> IO Term
getTerm syms p = do xs <- prompt p
                    let s = evalT syms xs
                    case s of
                       (Right s) -> return s
                       (Left errMsg) -> putStrLn errMsg >> getTerm syms p

getSymbols :: String -> IO [Symbol]
getSymbols p = do xs <- prompt p
                  let s = evalSyms xs
                  case s of
                     (Right s) -> return s
                     (Left errMsg) -> putStrLn errMsg >> getSymbols p

runEngine :: IO Bool
runEngine = do syms <- getSymbols "Input a list of constant, function and relation symbols: "
               s <- getSequent syms "Input a sequent: "
               case s of
                 (_ `Entails` _) -> applyRule'' syms s
                 (a `Biconditional` c) -> do
                   res1 <- applyRule'' syms ([a] `Entails` c)
                   res2 <- applyRule'' syms ([c] `Entails` a)
                   return $ res1 && res2

runEngine' :: IO ()
runEngine' = do syms <- getSymbols "Input a list of constant, function and relation symbols: "
                x <- getPred syms "Input a predicate formula: "
                t <- getTerm syms "Enter a term to sub in: "
                v <- getTerm syms "Enter a variable to sub: "
                print x
                print $ rmDupes (vars x)
                print $ rmDupes (freeVars x)
                print $ rmDupes (boundVars x)
                print $ sub t v x
                return ()