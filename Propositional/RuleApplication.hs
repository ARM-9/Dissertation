module Propositional.RuleApplication(
  RuleApplication(..),
  applyRule
) where

import Propositional.Sequent
import Propositional.Prop
import Propositional.Rule
import Utils
import Data.List

data RuleApplication = UndoingApplication
                     | InvalidApplication   String
                     | SingleApplication    Sequent
                     | BranchingApplication Sequent Sequent

andI :: Sequent -> Prop -> Prop -> RuleApplication
andI (as `Entails` c) p q
  | p `elem` as && q `elem` as = SingleApplication (setApp (p `And` q) as `Entails` c)
  | otherwise = InvalidApplication "One or both propositions are not in scope"
andI _ _ _ = errorBiconditional

andEl :: Sequent -> Prop -> RuleApplication
andEl (as `Entails` c) (p `And` q)
  | (p `And` q) `elem` as = SingleApplication (setApp p as `Entails` c)
  | otherwise = InvalidApplication "Proposition not in scope"
andEl (_ `Entails` _) _ = InvalidApplication "Conjunctive proposition must be provided"
andEl _ _ = errorBiconditional

andEr :: Sequent -> Prop -> RuleApplication
andEr s (p `And` q) = andEl s (q `And` p)

impI :: Sequent -> RuleApplication
impI (as `Entails` (p `Imp` q)) = SingleApplication (setPre p as `Entails` q)
impI (_ `Entails` _) = InvalidApplication "Consequent must be an implicative proposition"
impI _ = errorBiconditional

impE :: Sequent -> Prop -> Prop -> RuleApplication
impE (as `Entails` c) (p `Imp` q) r
  | notInScope = InvalidApplication "One or both propositions are not in scope"
  | fallacy = InvalidApplication "Premise of provided implication does not match provided proposition"
  | otherwise = SingleApplication (setApp q as `Entails` c)
  where notInScope = (p `Imp` q) `notElem` as || r `notElem` as
        fallacy = p /= r
impE (as `Entails` c) r (p `Imp` q) = impE (as `Entails` c) (p `Imp` q) r
impE (_ `Entails` _) _ _ = InvalidApplication "Implicative proposition must be provided"
impE _ _ _ = errorBiconditional

orIl :: Sequent -> Prop -> RuleApplication
orIl (as `Entails` c) (p `Or` q)
  | p `elem` as = SingleApplication (setApp (p `Or` q) as `Entails` c)
  | otherwise = InvalidApplication "Proposition not in scope"
orIl (_ `Entails` _) _ = InvalidApplication "Disjunctive proposition must be provided"
orIl _ _ = errorBiconditional

orIr :: Sequent -> Prop -> RuleApplication
orIr s (p `Or` q) = orIl s (q `Or` p)

orE :: Sequent -> Prop -> RuleApplication
orE (as `Entails` c) (p `Or` q)
  | (p `Or` q) `elem` as = BranchingApplication (setPre p as `Entails` c) (setPre q as `Entails` c)
  | otherwise = InvalidApplication "Proposition not in scope"
orE (_ `Entails` _) p = InvalidApplication "Disjunctive proposition must be provided"
orE _ _ = errorBiconditional

notI :: Sequent -> RuleApplication
notI (as `Entails` (Not p)) = SingleApplication (setPre p as `Entails` Const False)
notI (_ `Entails` _) = InvalidApplication "Consequent must be a negative proposition"
notI _ = errorBiconditional

notE :: Sequent -> Prop -> Prop -> RuleApplication
notE (as `Entails` c) p (Not q)
  | notInScope = InvalidApplication "One or both propositions are not in scope"
  | fallacy = InvalidApplication "Propositions must be negations of eachother"
  | otherwise = SingleApplication (setApp (Const False) as `Entails` c)
  where notInScope = p `notElem` as || Not q `notElem` as
        fallacy = p /= q
notE s (Not q) p = notE s p (Not q)
notE _ _ _ = errorBiconditional

topI :: Sequent -> RuleApplication
topI (as `Entails` c) = SingleApplication (setApp (Const True) as `Entails` c)
topI _ = errorBiconditional

botE :: Sequent -> Prop -> RuleApplication
botE (as `Entails` c) p
  | Const False `elem` as = SingleApplication (setApp p as `Entails` c)
  | otherwise = InvalidApplication "Bottom proposition not in scope"
botE _ _ = errorBiconditional

lemmaI :: Sequent -> Prop -> RuleApplication
lemmaI (as `Entails` c) p = BranchingApplication (as `Entails` p) (setApp p as `Entails` c)
lemmaI _ _ = errorBiconditional

pbc :: Sequent -> RuleApplication
pbc (as `Entails` c) = SingleApplication (setPre (Not c) as `Entails` Const False)
pbc _ = errorBiconditional

errorBiconditional :: RuleApplication
errorBiconditional = InvalidApplication "Function undefined for biconditionals"

applyRule'' :: Sequent -> Rule -> RuleApplication
applyRule'' s rule = case rule of
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
       Pbc              -> pbc    s
       Undo             -> UndoingApplication

applyRule' :: Sequent -> IO Bool
applyRule' s = do
  print s
  r <- getRule
  let ruleApl = applyRule'' s r
  case ruleApl of
    InvalidApplication str -> do
      putStrLn $ "Error: " ++ str
      applyRule' s
    SingleApplication s1 -> do
       result <- applyRule s1
       if not result then
          applyRule' s
       else return True
    BranchingApplication s1 s2 -> do
       result1 <- applyRule s1
       result2 <- applyRule s2
       if not (result1 && result2) then
          applyRule' s
       else return True
    UndoingApplication -> return False

applyRule :: Sequent -> IO Bool
applyRule s = do if isTrivial s then return True else applyRule' s
