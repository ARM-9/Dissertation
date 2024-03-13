{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Predicate(
    Pred(..),
    Term(..),
) where

import Data.List (intercalate, nub)
import Control.Applicative hiding (Const)
import Parser
import Data.Maybe
import System.Console.Haskeline
import GHC.OldList(intersect)
import Data.Char (isDigit, intToDigit)
import Debug.Trace (trace)

prettyArgs :: Show t => [t] -> String
prettyArgs [] = ""
prettyArgs ts = "(" ++ intercalate ", " (map show ts) ++ ")"

combine :: Eq a => [a] -> [a] -> [a]
combine xs ys = nub $ xs ++ ys

--------------------
{- Pred data type -}
--------------------

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

--------------------
{- Term data type -}
--------------------

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

isFree :: Term -> Bool
isFree (Var x) = all isDigit x
isFree _ = False

newFreeVar :: [Term] -> Term
newFreeVar vs = Var $ show index
  where index = length (filter isFree vs)

-------------------------------------------------
{- Recursive functions over predicate formulae -}
-------------------------------------------------

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

varsT :: Term -> [Term]
varsT (Var v)     = [Var v]
varsT (ConstT _)  = []
varsT (Func _ ts) = nub $ concatMap varsT ts

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

subT :: Term -> Term -> Term -> Term
subT t (Var x) (Var y) = if x == y then t else Var y
subT _ _ (ConstT c)    = ConstT c
subT t v (Func f ts)   = Func f (map (subT t v) ts)
subT _ _ t             = t

-----------------------
{- Sequent data type -}
-----------------------

data Sequent = ([Term], [Pred]) `Entails` Pred
             | ([Term], Pred) `Biconditional` Pred

-- TODO: make a pretty print for sequents
instance Show Sequent where
  show :: Sequent -> String
  show ((_, antecedents) `Entails` consequent) =
    intercalate ", " [show antecedents] ++ " ⊢ " ++ show consequent
  show ((_, antecedent) `Biconditional` consequent) =
    show antecedent ++ " ⟛ " ++ show consequent

-----------------
{- Pred parser -}
-----------------

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

-----------------
{- Term parser -}
-----------------

-- Does not check to see if variables and free
-- vars are in scope; simply parses and checking
-- logic is to be completed by the calling function
termP :: [Symbol] -> Parser Term
termP syms = do f <- lowerStr
                case getSym f syms of
                     Just (Function _ arity) -> do symbol "("
                                                   ts <- listN arity $ termP syms
                                                   symbol ")"
                                                   return $ Func f ts
                     _                       -> empty
      <|> do x <- lowerStr
             case getSym x syms of
                  Nothing           -> return $ Var x
                  Just (Constant _) -> return $ ConstT x
                  _                 -> empty
      <|> do Var . show <$> number

evalT :: [Symbol] -> String -> Either String Term
evalT syms = eval (termP syms)

--------------------
{- Sequent parser -}
--------------------

sequentP :: [Symbol] -> Parser Sequent
sequentP syms = do l <- l1P syms
                   do symbol "|-" <|> symbol "⊢"
                      r <- l1P syms
                      return (([], [l]) `Entails` r)
                    <|> do symbol "-||-" <|> symbol "⟛"
                           r <- l1P syms
                           return (([], l) `Biconditional` r)
                <|> do ls <- list $ l1P syms
                       symbol "|-" <|> symbol "⊢"
                       r <- l1P syms
                       return (([], ls) `Entails` r)
                <|> do symbol "|-" <|> symbol "⊢"
                       r <- l1P syms
                       return (([], []) `Entails` r)

evalS :: [Symbol] -> String -> Either String Sequent
evalS syms = eval (sequentP syms)

----------------------
{- Symbol data type -}
----------------------

data Symbol = Constant String
            | Function String Int
            | Relation String Int
            deriving (Eq)

instance Show Symbol where
   show :: Symbol -> String
   show (Constant c) = c
   show (Function f n) = f ++ "(" ++ show n ++ ")"
   show (Relation r n) = r ++ "(" ++ show n ++ ")"

getSym :: String -> [Symbol] -> Maybe Symbol
getSym _ [] = Nothing
getSym xs (Constant sym : syms)
  | xs == sym = Just (Constant sym)
  | otherwise = getSym xs syms
getSym xs (Function sym arity : syms)
  | xs == sym = Just (Function sym arity)
  | otherwise = getSym xs syms
getSym xs (Relation sym arity : syms)
  | xs == sym = Just (Relation sym arity)
  | otherwise = getSym xs syms

----------------------
{- Symbol parser -}
----------------------

arityP :: Parser Int
arityP = do symbol "("
            n <- number
            symbol ")"
            return n

symbolP :: [Symbol] -> Parser Symbol
symbolP syms = do r <- upperStartStr
                  case getSym r syms of
                       Nothing -> Relation r <$> arityP
                       _       -> empty
              <|> do f <- lowerStr
                     case getSym f syms of
                          Nothing -> Function f <$> arityP
                          _       -> empty
              <|> do c <- lowerStr
                     case getSym c syms of
                          Nothing -> return $ Constant c
                          _       -> empty

symbolsP :: [Symbol] -> Parser [Symbol]
symbolsP syms = do sym <- symbolP syms
                   do comma
                      otherSyms <- symbolsP (sym : syms)
                      return (sym : otherSyms)
                    <|> return [sym]
               <|> do symbol "-"
                      return []

evalSyms :: String -> Either String [Symbol]
evalSyms = eval (symbolsP [])

--------------------
{- Rule data type -}
--------------------

data Rule = Undo
          | AndIntro   Pred Pred
          | AndElimL   Pred
          | AndElimR   Pred
          | ImpIntro
          | ImpElim    Pred Pred
          | OrIntroL   Pred
          | OrIntroR   Pred
          | OrELim     Pred
          | NotIntro
          | NotELim    Pred Pred
          | TopIntro
          | BottomElim Pred
          | AllIntro
          | AllElim    Pred Term
          | ExiIntro   Pred Term Term
          | ExiElim    Pred
          | LemmaIntro Pred
          | Pbc
          deriving (Show) -- Add instance show

--------------------
{- Rule parser -}
--------------------

ruleP :: [Symbol] -> Parser Rule
ruleP syms = do (p, q) <- binaryRuleP syms "ANDI"
                return $ AndIntro p q
            <|> do p <- unaryRuleP syms "ANDEL"
                   return $ AndElimL p
            <|> do p <- unaryRuleP syms "ANDEL"
                   return $ AndElimR p
            <|> do symbol "IMPI"
                   return ImpIntro
            <|> do (p, q) <- binaryRuleP syms "IMPE"
                   return $ ImpElim p q
            <|> do p <- unaryRuleP syms "ORIL"
                   return $ OrIntroL p
            <|> do p <- unaryRuleP syms "ORIL"
                   return $ OrIntroR p
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
            <|> do symbol "ALLI"
                   return AllIntro
            <|> do symbol "ALLE"
                   comma
                   p <- l1P syms
                   comma
                   t <- termP syms
                   return $ AllElim p t
            <|> do symbol "EXII"
                   comma
                   p <- l1P syms
                   comma
                   t <- termP syms
                   comma
                   ExiIntro p t <$> termP syms
            <|> do p <- unaryRuleP syms "EXIE"
                   return $ ExiElim p
            <|> do p <- unaryRuleP syms "LEMMAI"
                   return $ LemmaIntro p
            <|> do p <- symbol "PBC"
                   return Pbc
            <|> do symbol "UNDO" >> return Undo

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

----------------------
{- Rule application -}
----------------------

data RuleApplication = UndoingApplication
                     | InvalidApplication   String
                     | SingleApplication    Sequent
                     | BranchingApplication Sequent Sequent

andI :: Sequent -> Pred -> Pred -> RuleApplication
andI ((vs, as) `Entails` c) p q
  | p `elem` as && q `elem` as = SingleApplication ((vs, combine as [p `And` q]) `Entails` c)
  | otherwise = InvalidApplication "One or both propositions are not in scope"
andI _ _ _ = errorBiconditional

andEl :: Sequent -> Pred -> RuleApplication
andEl ((vs, as) `Entails` c) (p `And` q)
  | (p `And` q) `elem` as = SingleApplication ((vs, combine as [p]) `Entails` c)
  | otherwise = InvalidApplication "Proposition not in scope"
andEl (_ `Entails` _) _ = InvalidApplication "Conjunctive proposition must be provided"
andEl _ _ = errorBiconditional

andEr :: Sequent -> Pred -> RuleApplication
andEr s (p `And` q) = andEl s (q `And` p)

impI :: Sequent -> RuleApplication
impI ((vs, as) `Entails` (p `Imp` q)) = SingleApplication ((vs, combine as [p]) `Entails` q)
impI (_ `Entails` _) = InvalidApplication "Consequent must be an implicative proposition"
impI _ = errorBiconditional

impE :: Sequent -> Pred -> Pred -> RuleApplication
impE ((vs, as) `Entails` c) (p `Imp` q) r
  | x && y && z = SingleApplication ((vs, combine as [q]) `Entails` c)
  | x && y = InvalidApplication "Premise of provided implication does not match provided proposition"
  | otherwise = InvalidApplication "One or both propositions are not in scope"
  where x = (p `Imp` q) `elem` as
        y = r `elem` as
        z = p == r
impE ((vs, as) `Entails` c) r (p `Imp` q) = impE ((vs, as) `Entails` c) (p `Imp` q) r
impE (_ `Entails` _) _ _ = InvalidApplication "Implicative proposition must be provided"
impE _ _ _ = errorBiconditional

orIl :: Sequent -> Pred -> RuleApplication
orIl ((vs, as) `Entails` c) (p `Or` q)
  | p `elem` as = SingleApplication ((combine vs (vars q), combine as [p `Or` q]) `Entails` c)
  | otherwise = InvalidApplication "Proposition not in scope"
orIl (_ `Entails` _) _ = InvalidApplication "Disjunctive proposition must be provided"
orIl _ _ = errorBiconditional

orIr :: Sequent -> Pred -> RuleApplication
orIr s (p `Or` q) = orIl s (q `Or` p)

orE :: Sequent -> Pred -> RuleApplication
orE ((vs, as) `Entails` c) (p `Or` q)
  | (p `Or` q) `elem` as = BranchingApplication ((vs, p:as) `Entails` c) ((vs, q:as) `Entails` c)
  | otherwise = InvalidApplication "Proposition not in scope"
orE (_ `Entails` _) p = trace (show p) InvalidApplication "Disjunctive proposition must be provided"
orE _ _ = errorBiconditional

notI :: Sequent -> RuleApplication
notI ((vs, as) `Entails` (Not p)) = SingleApplication ((vs, p:as) `Entails` Const False)
notI (_ `Entails` _) = InvalidApplication "Consequent must be a negative proposition"
notI _ = errorBiconditional

notE :: Sequent -> Pred -> Pred -> RuleApplication
notE ((vs, as) `Entails` c) p (Not q)
  | x && y && z = SingleApplication ((vs, combine as [Const False]) `Entails` c)
  | x && y = InvalidApplication "Propositions must be negations of eachother"
  | otherwise = InvalidApplication "One or both propositions are not in scope"
  where x = p `elem` as
        y = Not q `elem` as
        z = p == q
notE s (Not q) p = notE s p (Not q)
notE _ _ _ = errorBiconditional

topI :: Sequent -> RuleApplication
topI ((vs, as) `Entails` c) = SingleApplication ((vs, combine as [Const True]) `Entails` c)
topI _ = errorBiconditional

botE :: Sequent -> Pred -> RuleApplication
botE ((vs, as) `Entails` c) p
  | Const False `elem` as = SingleApplication ((combine vs (vars p), combine as [p]) `Entails` c)
  | otherwise = InvalidApplication "Bottom proposition not in scope"
botE _ _ = errorBiconditional

lemmaI :: Sequent -> Pred -> RuleApplication
lemmaI ((vs, as) `Entails` c) p = BranchingApplication ((combine vs (vars p), as) `Entails` p)
                                                       ((combine vs (vars p), combine as [p]) `Entails` c)
lemmaI _ _ = errorBiconditional

allI :: Sequent -> RuleApplication
allI ((vs, as) `Entails` (All v p)) = SingleApplication ((freeVar : vs, as) `Entails` subbedP)
  where freeVar = newFreeVar vs
        subbedP = sub freeVar (Var v) p
allI (_ `Entails` _) = InvalidApplication "Consequent must be universally quantified"
allI _ = errorBiconditional

allE :: Sequent -> Pred -> Term -> RuleApplication
allE ((vs, as) `Entails` c) (All v q) t
  | x && y = SingleApplication ((combine vs (varsT t), combine as [subbedTQ]) `Entails` c)
  | x = InvalidApplication "Substituting provided term will result in variable capture"
  | otherwise = InvalidApplication "Universally quantified proposition not in scope"
  where x = All v q `elem` as
        y = null (varsT t `intersect` boundVars q)
        subbedTQ = sub t (Var v) q
allE (_ `Entails` _) _ _ = InvalidApplication "Provided proposition must be universally quantified"
allE _ _ _ = errorBiconditional

exiI :: Sequent -> Pred -> Term -> Term -> RuleApplication
exiI ((vs, as) `Entails` c) p t (Var v)
  | vBound = InvalidApplication "Provided variable is already bound"
  | varCapture = InvalidApplication "Substituting provided term will result in variable capture"
  | otherwise = SingleApplication ((combine vs $ combine (varsT t) [Var v], combine as [generalisedP]) `Entails` c)
  where vBound = Var v `elem` boundVars p
        varCapture = not . null $ varsT t `intersect` boundVars p
        subbedP = sub (Var v) t p
        generalisedP = Exi v subbedP
exiI _ _ _ _ = errorBiconditional

exiE :: Sequent -> Pred -> RuleApplication
exiE ((vs, as) `Entails` c) (Exi v q)
  | Exi v q `elem` as = SingleApplication ((freeVar : vs, subbedQ : as) `Entails` c)
  | otherwise = InvalidApplication "Propostion not in scope"
  where freeVar = newFreeVar vs
        subbedQ = sub freeVar (Var v) q
exiE (_ `Entails` _) _ = InvalidApplication "Proposition must be existentially quantified"
exiE _ _ = errorBiconditional

pbc :: Sequent -> RuleApplication
pbc ((vs, as) `Entails` c) = SingleApplication ((vs, Not c : as) `Entails` Const False)
pbc _ = errorBiconditional

errorBiconditional :: RuleApplication
errorBiconditional = InvalidApplication "Function undefined for biconditionals"

applyRule :: Sequent -> Rule -> RuleApplication
applyRule s rule = case rule of
       (AndIntro p q)   -> andI   s p q
       (AndElimL p)     -> andEl  s p
       (AndElimR p)     -> andEr  s p
       ImpIntro         -> impI   s
       (ImpElim p q)    -> impE   s p q
       (OrIntroL p)     -> orIl   s p
       (OrIntroR p)     -> orIr   s p
       (OrELim p)       -> orE    s p
       NotIntro         -> notI   s
       (NotELim p q)    -> notE   s p q
       TopIntro         -> topI   s
       (BottomElim p)   -> botE   s p
       (LemmaIntro p)   -> lemmaI s p
       AllIntro         -> allI   s
       (AllElim p t)    -> allE   s p t
       (ExiIntro p t v) -> exiI   s p t v
       (ExiElim p)      -> exiE   s p
       Pbc              -> pbc    s
       Undo             -> UndoingApplication

applyRule' :: [Symbol] -> Sequent -> IO Bool
applyRule' syms s = do
  print s
  r <- getRule syms "Enter a rule: "
  let ruleApl = applyRule s r
  case ruleApl of
    InvalidApplication str -> do
      putStrLn $ "Error: " ++ str
      applyRule' syms s
    SingleApplication s1 -> do
       result <- applyRule'' syms s1
       if not result then
          applyRule' syms s
       else return True
    BranchingApplication s1 s2 -> do
       result1 <- applyRule'' syms s1
       result2 <- applyRule'' syms s2
       if not (result1 && result2) then
          applyRule' syms s
       else return True
    UndoingApplication -> return False

applyRule'' :: [Symbol] -> Sequent -> IO Bool
applyRule'' syms s = do if solved s then return True else applyRule' syms s

getRule :: [Symbol] -> String -> IO Rule
getRule syms text = do
  input <- prompt text
  case evalR syms input of
    Right rule -> return rule
    Left errMsg -> putStrLn errMsg >> getRule syms text

solved :: Sequent -> Bool
solved ((_, as) `Entails` c) = c `elem` as

prompt :: String -> IO String
prompt text = runInputT defaultSettings $ do
  getInputLine text >>= \case
    Nothing   -> return ""
    Just line -> return line

extractVars :: Sequent -> Sequent
extractVars ((_, as) `Entails` c) = (nub $ concatMap vars as ++ vars c, as) `Entails` c
extractVars ((_, a) `Biconditional` c) = (nub $ vars a ++ vars c, a) `Biconditional` c

getSequent :: [Symbol] -> String -> IO Sequent
getSequent syms p = do xs <- prompt p
                       let s = evalS syms xs
                       case s of
                         (Right s) -> return $ extractVars s
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
                 ((vs, a) `Biconditional` c) -> do
                   res1 <- applyRule'' syms ((vs, [a]) `Entails` c)
                   res2 <- applyRule'' syms ((vs, [c]) `Entails` a)
                   return $ res1 && res2
