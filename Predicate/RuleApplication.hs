module Predicate.RuleApplication(
  RuleApplication(..),
  applyRule
) where

import Predicate.Sequent
import Predicate.Pred
import Predicate.Term
import Predicate.Symbol
import Predicate.Rule
import Utils
import Data.List
import System.Console.Haskeline

data RuleApplication = UndoingApplication
                     | InvalidApplication   String
                     | LinearApplication    Sequent
                     | BranchingApplication Sequent Sequent

andI :: Sequent -> Pred -> Pred -> RuleApplication
andI ((vs, as) `Entails` c) p q
  | p `elem` as && q `elem` as = LinearApplication ((vs, setApp (p `And` q) as) `Entails` c)
  | otherwise = InvalidApplication "One or both propositions are not in scope"

andEl :: Sequent -> Pred -> RuleApplication
andEl ((vs, as) `Entails` c) (p `And` q)
  | (p `And` q) `elem` as = LinearApplication ((vs, setApp p as) `Entails` c)
  | otherwise = InvalidApplication "Proposition not in scope"
andEl (_ `Entails` _) _ = InvalidApplication "Conjunctive proposition must be provided"

andEr :: Sequent -> Pred -> RuleApplication
andEr s (p `And` q) = andEl s (q `And` p)

impI :: Sequent -> RuleApplication
impI ((vs, as) `Entails` (p `Imp` q)) = LinearApplication ((vs, setPre p as) `Entails` q)
impI (_ `Entails` _) = InvalidApplication "Consequent must be an implicative proposition"

impE :: Sequent -> Pred -> Pred -> RuleApplication
impE ((vs, as) `Entails` c) (p `Imp` q) r
  | notInScope = InvalidApplication "One or both propositions are not in scope"
  | fallacy = InvalidApplication "Premise of provided implication does not match provided proposition"
  | otherwise = LinearApplication ((vs, setApp q as) `Entails` c)
  where notInScope = (p `Imp` q) `notElem` as || r `notElem` as
        fallacy = p /= r
impE ((vs, as) `Entails` c) r (p `Imp` q) = impE ((vs, as) `Entails` c) (p `Imp` q) r
impE (_ `Entails` _) _ _ = InvalidApplication "Implicative proposition must be provided"

orIl :: Sequent -> Pred -> RuleApplication
orIl ((vs, as) `Entails` c) (p `Or` q)
  | p `elem` as = LinearApplication ((mergeSets vs (vars q), setApp (p `Or` q) as) `Entails` c)
  | otherwise = InvalidApplication "Proposition not in scope"
orIl (_ `Entails` _) _ = InvalidApplication "Disjunctive proposition must be provided"

orIr :: Sequent -> Pred -> RuleApplication
orIr s (p `Or` q) = orIl s (q `Or` p)

orE :: Sequent -> Pred -> RuleApplication
orE ((vs, as) `Entails` c) (p `Or` q)
  | (p `Or` q) `elem` as = BranchingApplication ((vs, setPre p as) `Entails` c) ((vs, setPre q as) `Entails` c)
  | otherwise = InvalidApplication "Proposition not in scope"
orE (_ `Entails` _) p = InvalidApplication "Disjunctive proposition must be provided"

notI :: Sequent -> RuleApplication
notI ((vs, as) `Entails` (Not p)) = LinearApplication ((vs, setPre p as) `Entails` Const False)
notI (_ `Entails` _) = InvalidApplication "Consequent must be a negative proposition"

notE :: Sequent -> Pred -> Pred -> RuleApplication
notE ((vs, as) `Entails` c) p (Not q)
  | notInScope = InvalidApplication "One or both propositions are not in scope"
  | fallacy = InvalidApplication "Propositions must be negations of eachother"
  | otherwise = LinearApplication ((vs, setApp (Const False) as) `Entails` c)
  where notInScope = p `notElem` as || Not q `notElem` as
        fallacy = p /= q
notE s (Not q) p = notE s p (Not q)

topI :: Sequent -> RuleApplication
topI ((vs, as) `Entails` c) = LinearApplication ((vs, setApp (Const True) as) `Entails` c)

botE :: Sequent -> Pred -> RuleApplication
botE ((vs, as) `Entails` c) p
  | Const False `elem` as = LinearApplication ((mergeSets vs (vars p), setApp p as) `Entails` c)
  | otherwise = InvalidApplication "Bottom proposition not in scope"

lemmaI :: Sequent -> Pred -> RuleApplication
lemmaI ((vs, as) `Entails` c) p = BranchingApplication ((mergeSets vs (vars p), as) `Entails` p)
                                                       ((mergeSets vs (vars p), setApp p as) `Entails` c)

allI :: Sequent -> RuleApplication
allI ((vs, as) `Entails` (All v p)) = LinearApplication ((setApp freeVar vs, as) `Entails` subbedP)
  where freeVar = newFreeVar vs
        subbedP = sub freeVar (Var v) p
allI (_ `Entails` _) = InvalidApplication "Consequent must be universally quantified"

allE :: Sequent -> Pred -> Term -> RuleApplication
allE ((vs, as) `Entails` c) (All v q) t
  | notInScope = InvalidApplication "Universally quantified proposition not in scope"
  | varCapture = InvalidApplication "Substituting in provided term will result in variable capture"
  | otherwise = LinearApplication ((mergeSets vs (varsT t), setApp subbedTQ as) `Entails` c)
  where notInScope = All v q `notElem` as
        varCapture = not . null $ varsT t `intersect` boundVars q
        subbedTQ = sub t (Var v) q
allE (_ `Entails` _) _ _ = InvalidApplication "Provided proposition must be universally quantified"

exiI :: Sequent -> Pred -> Term -> Variable -> RuleApplication
exiI ((vs, as) `Entails` c) p t (Var v)
  | termNotInPred = InvalidApplication "Provided term does not appear in the formula provided"
  | varBound = InvalidApplication "Provided variable is already bound"
  | varCapture = InvalidApplication "Substituting in provided term will result in variable capture"
  | otherwise = LinearApplication ((mergeSets vs $ setApp  (Var v) (varsT t), setApp generalisedP as) `Entails` c)
  where termNotInPred = t `notElem` terms p
        varBound = Var v `elem` boundVars p
        varCapture = not . null $ varsT t `intersect` boundVars p
        subbedP = sub (Var v) t p
        generalisedP = Exi v subbedP

exiE :: Sequent -> Pred -> RuleApplication
exiE ((vs, as) `Entails` c) (Exi v p)
  | Exi v p `elem` as = LinearApplication ((setApp freeVar vs, setPre subbedP as) `Entails` c)
  | otherwise = InvalidApplication "Propostion not in scope"
  where freeVar = newFreeVar vs
        subbedP = sub freeVar (Var v) p
exiE (_ `Entails` _) _ = InvalidApplication "Proposition must be existentially quantified"

pbc :: Sequent -> RuleApplication
pbc ((vs, as) `Entails` c) = LinearApplication ((vs, setPre (Not c) as) `Entails` Const False)

applyRule'' :: Sequent -> Rule -> RuleApplication
applyRule'' s rule = case rule of
       (AndIntro p q)   -> andI   s p q
       (AndElimL p)     -> andEl  s p
       (AndElimR p)     -> andEr  s p
       ImpIntro         -> impI   s
       (ImpElim p q)    -> impE   s p q
       (OrIntroL p)     -> orIl   s p
       (OrIntroR p)     -> orIr   s p
       (OrElim p)       -> orE    s p
       NotIntro         -> notI   s
       (NotElim p q)    -> notE   s p q
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
  r <- getRule syms
  let ruleApl = applyRule'' s r
  case ruleApl of
    InvalidApplication str -> do
      putStrLn $ "Error: " ++ str
      applyRule' syms s
    LinearApplication s1 -> do
       result <- applyRule syms s1
       if not result then
          applyRule' syms s
       else return True
    BranchingApplication s1 s2 -> do
       result1 <- applyRule syms s1
       result2 <- applyRule syms s2
       if not (result1 && result2) then
          applyRule' syms s
       else return True
    UndoingApplication -> return False

applyRule :: [Symbol] -> Sequent -> IO Bool
applyRule syms s = do if identity s then return True else applyRule' syms s
