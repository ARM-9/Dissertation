module Predicate.Rule(
  Rule(..),
  evalR
) where

import Predicate.Pred
import Predicate.Term
import Predicate.Symbol
import Parser
import Control.Applicative

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