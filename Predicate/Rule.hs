module Predicate.Rule(
  Rule(..),
  getRule
) where

import Predicate.Pred
import Predicate.Term
import Predicate.Symbol
import Parser
import Utils
import Control.Applicative

data Rule = Undo
          | AndIntro   Pred Pred
          | AndElimL   Pred
          | AndElimR   Pred
          | ImpIntro
          | ImpElim    Pred Pred
          | OrIntroL   Pred
          | OrIntroR   Pred
          | OrElim     Pred
          | NotIntro
          | NotElim    Pred Pred
          | BiconIntro
          | BiconElim  Pred Pred
          | TopIntro
          | BottomElim Pred
          | AllIntro
          | AllElim    Pred Term
          | ExiIntro   Pred Term Variable
          | ExiElim    Pred
          | EqualIntro Term
          | EqualElim  Pred Pred
          | LemmaIntro Pred
          | Pbc
          deriving (Show)

ruleP :: Signature -> Parser Rule
ruleP syms = do (p, q) <- binaryRuleP syms "ANDI"
                return $ AndIntro p q
            <|> do p <- unaryRuleP syms "ANDEL"
                   return $ AndElimL p
            <|> do p <- unaryRuleP syms "ANDER"
                   return $ AndElimR p
            <|> do symbol "IMPI"
                   return ImpIntro
            <|> do (p, q) <- binaryRuleP syms "IMPE"
                   return $ ImpElim p q
            <|> do p <- unaryRuleP syms "ORIL"
                   return $ OrIntroL p
            <|> do p <- unaryRuleP syms "ORIR"
                   return $ OrIntroR p
            <|> do p <- unaryRuleP syms "ORE"
                   return $ OrElim p
            <|> do symbol "NOTI"
                   return NotIntro
            <|> do (p, q) <- binaryRuleP syms "NOTE"
                   return $ NotElim p q
            <|> do symbol "TOPI"
                   return TopIntro
            <|> do p <- unaryRuleP syms "BOTE"
                   return $ BottomElim p
            <|> do symbol "ALLI"
                   return AllIntro
            <|> do symbol "ALLE"
                   comma
                   p <- predP syms
                   comma
                   t <- termP syms
                   return $ AllElim p t
            <|> do symbol "EXII"
                   comma
                   p <- predP syms
                   comma
                   t <- termP syms
                   comma
                   ExiIntro p t <$> termP syms
            <|> do p <- unaryRuleP syms "EXIE"
                   return $ ExiElim p
            <|> do symbol "EQUALI"
                   comma
                   t <- termP syms
                   return $ EqualIntro t
            <|> do (p, q) <- binaryRuleP syms "EQUALE"
                   return $ EqualElim p q
            <|> do p <- unaryRuleP syms "LEMMAI"
                   return $ LemmaIntro p
            <|> do p <- symbol "PBC"
                   return Pbc
            <|> do symbol "UNDO" >> return Undo

unaryRuleP :: Signature -> String -> Parser Pred
unaryRuleP syms rule = do symbol rule
                          comma
                          predP syms

binaryRuleP :: Signature -> String -> Parser (Pred, Pred)
binaryRuleP syms rule = do symbol rule
                           comma
                           p <- predP syms
                           comma
                           q <- predP syms
                           return (p, q)

evalR :: Signature -> String -> Either String Rule
evalR syms = eval (ruleP syms)

getRule :: Signature -> IO Rule
getRule syms = do input <- prompt "Enter a rule: "
                  case evalR syms input of
                       Right rule -> return rule
                       Left errMsg -> putStrLn errMsg >> getRule syms