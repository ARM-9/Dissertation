module Propositional.Rule(
  Rule(..),
  getRule
) where

import Propositional.Prop
import Parser
import Utils
import Control.Applicative

data Rule = Undo
          | AndIntro   Prop Prop
          | AndElimL   Prop
          | AndElimR   Prop
          | ImpIntro
          | ImpElim    Prop Prop
          | OrIntroL   Prop
          | OrIntroR   Prop
          | OrELim     Prop
          | NotIntro
          | NotELim    Prop Prop
          | BiconIntro
          | BiconElim  Prop Prop
          | TopIntro
          | BottomElim Prop
          | LemmaIntro Prop
          | Pbc
          deriving (Show)

ruleP :: Parser Rule
ruleP = do (p, q) <- binaryRuleP "ANDI"
           return $ AndIntro p q
       <|> do p <- unaryRuleP "ANDEL"
              return $ AndElimL p
       <|> do p <- unaryRuleP "ANDER"
              return $ AndElimR p
       <|> do symbol "IMPI"
              return ImpIntro
       <|> do (p, q) <- binaryRuleP "IMPE"
              return $ ImpElim p q
       <|> do p <- unaryRuleP "ORIL"
              return $ OrIntroL p
       <|> do p <- unaryRuleP "ORIL"
              return $ OrIntroR p
       <|> do p <- unaryRuleP "ORE"
              return $ OrELim p
       <|> do symbol "NOTI"
              return NotIntro
       <|> do (p, q) <- binaryRuleP "NOTE"
              return $ NotELim p q
       <|> do symbol "TOPI"
              return TopIntro
       <|> do p <- unaryRuleP "BOTE"
              return $ BottomElim p
       <|> do p <- unaryRuleP "LEMMAI"
              return $ LemmaIntro p
       <|> do p <- symbol "PBC"
              return Pbc
       <|> do symbol "UNDO" >> return Undo

unaryRuleP :: String -> Parser Prop
unaryRuleP rule = do symbol rule
                     comma
                     propP

binaryRuleP :: String -> Parser (Prop, Prop)
binaryRuleP rule = do symbol rule
                      comma
                      p <- propP
                      comma
                      q <- propP
                      return (p, q)

evalR :: String -> Either String Rule
evalR = eval ruleP

getRule :: IO Rule
getRule = do input <- prompt "Enter a rule: "
             case evalR input of
                  Right rule -> return rule
                  Left errMsg -> putStrLn errMsg >> getRule