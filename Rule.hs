module Rule where
import Parser
import Control.Applicative hiding (Const)
import Formula
import Sequent

data Rule p = EmptyRule
          | AndIntro   p p
          | AndElimL   p
          | AndElimR   p
          | ImpIntro -- (Sequent p) -- xx
          | ImpElim    p p
          | OrIntroL   p p
          | OrIntroR   p p
          | OrELim     p p -- (Sequent p) (Sequent p) -- xx
          | NotIntro -- (Sequent p) -- xx
          | NotELim    p p
          | TopIntro
          | BottomElim p
          | StmtIntro  p
          | Pbc -- (Sequent p) -- xx
          deriving (Show, Read)

ruleP :: Formula p => Parser (Rule p)
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

unaryRuleP :: Formula p => String -> Parser p
unaryRuleP rule = do symbol rule
                     comma
                     formulaP

binaryRuleP :: Formula p => String -> Parser (p, p)
binaryRuleP rule = do symbol rule
                      comma
                      p <- formulaP
                      comma
                      q <- formulaP
                      return (p, q)

data RuleApplication p = ErroneousApplication String
                       | SingleApplication (Sequent p)
                       | BranchingApplication (Sequent p) (Sequent p)

setInsert :: Eq a => [a] -> a -> [a]
setInsert xs x = if x `elem` xs then xs else xs ++ [x]

errorBicond :: RuleApplication p
errorBicond = ErroneousApplication "Function undefined for biconditionals"

andI :: Sequent p -> p -> p -> RuleApplication p
andI (as `Entails` c) p q
    | p `elem` as && q `elem` as = SingleApplication (setInsert as (p `and` q) `Entails` c)
    | otherwise = ErroneousApplication "One or both positions are not in scope"
andI _ _ _ = errorBicond

andEl :: Sequent p -> p -> RuleApplication p
andEl (as `Entails` c) (p `and` q)
    | (p `and` q) `elem` as = SingleApplication (setInsert as p `Entails` c)
    | otherwise = ErroneousApplication "andEl: AND position not in scope"
andEl _ (_ `and` _) = errorBicond
andEl _ _ = ErroneousApplication "andEl: AND position must be provided"

andEr :: Sequent p -> p -> RuleApplication p
andEr (as `Entails` c) (p `and` q)
    | (p `and` q) `elem` as = SingleApplication (setInsert as q `Entails` c)
    | otherwise = ErroneousApplication "andEr: AND position not in scope"
andEr _ (_ `and` _) = errorBicond
andEr _ _ = ErroneousApplication "andEr: AND position must be provided"

impI :: Sequent p -> RuleApplication p
impI (as `Entails` (p `Imp` q)) = SingleApplication ((p : as) `Entails` q)
impI (_ `Entails` _) = ErroneousApplication "impI: Consequent must be an IMPLICATION"
impI _ = errorBicond

impE :: Sequent p -> p -> p -> RuleApplication p
impE (as `Entails` c) (p `Imp` q) r
    | p == r = SingleApplication (setInsert as q `Entails` c)
    | otherwise = ErroneousApplication "impE: Premise does not match provided position"
impE (as `Entails` c) r (p `Imp` q)
    | p == r = SingleApplication (setInsert as q `Entails` c)
    | otherwise = ErroneousApplication "impE: Premise does not match provided position"
impE (_ `Entails` _) _ _ = ErroneousApplication "impE: IMPLICATION position must be provided"
impE _ _ _ = errorBicond

orIl :: Sequent p -> p -> p -> RuleApplication p
orIl (as `Entails` c) p q
    | p `elem` as = SingleApplication (setInsert as (p `or` q) `Entails` c)
    | otherwise = ErroneousApplication "orIl: position not in scope"
orIl _ _ _ = errorBicond

orIr :: Sequent p -> p -> p -> RuleApplication p
orIr (as `Entails` c) p q
    | p `elem` as = SingleApplication (setInsert as (q `or` p) `Entails` c)
    | otherwise = ErroneousApplication "orIr: position not in scope"
orIr _ _ _ = errorBicond

orE :: Sequent p -> p -> p -> RuleApplication p
orE (as `Entails` _) (p `or` q) r
    | (p `or` q) `elem` as = BranchingApplication ((p :as) `Entails` r) ((q : as) `Entails` r)
    | otherwise = ErroneousApplication "orE: position not in scope"
orE (_ `Entails` _) _ _ = ErroneousApplication "orE: OR position must be provided"
orE _ _ _ = ErroneousApplication "orE: Function undefined for biconditionals"

notI :: Sequent p -> RuleApplication p
notI (as `Entails` (Not p)) = SingleApplication ((p : as) `Entails` const False)
notI (_ `Entails` _) = ErroneousApplication "notI: NOT position must be provided"
notI _ = errorBicond

notE :: Sequent p -> p -> p -> RuleApplication p
notE (as `Entails` c) p (Not q)
    | p `elem` as && Not q `elem` as && p == q = SingleApplication (setInsert as (const False) `Entails` c)
    | otherwise = ErroneousApplication "notE: One or both positions are not in scope"
notE (as `Entails` c) (Not q) p
    | p `elem` as && Not q `elem` as && p == q = SingleApplication (setInsert as (const False) `Entails` c)
    | otherwise = ErroneousApplication "notE: One or both positions are not in scope"
notE _ _ _ = errorBicond

topI :: Sequent p -> RuleApplication p
topI (as `Entails` c) = SingleApplication (setInsert as (const True) `Entails` c)
topI _ = errorBicond

botE :: Sequent p -> p -> RuleApplication p
botE (as `Entails` c) p
    | const False `elem` as = SingleApplication (setInsert as p `Entails` c)
    | otherwise = ErroneousApplication "botE: BOTTOM position not in scope"
botE _ _ = errorBicond

stmtI :: Sequent p -> p -> RuleApplication p
stmtI (as `Entails` c) p = BranchingApplication (as `Entails` p) (setInsert as p `Entails` c)
stmtI _ _ = errorBicond

pbc :: Sequent p -> RuleApplication p
pbc (as `Entails` c) = SingleApplication ((Not c : as) `Entails` const False)
pbc _ = errorBicond