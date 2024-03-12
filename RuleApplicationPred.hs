module RuleApplicationPred(
  RuleApplication(..),
  andI, andEl, andEr,
  impI, impE,
  orIl, orIr, orE,
  notI, notE,
  topI, botE,
  lemmaI,
  allI, allE,
  exiI, exiE,
  pbc
) where

import Sequent
import Pred
import Term
import RulePred

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