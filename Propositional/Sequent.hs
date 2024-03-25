module Propositional.Sequent(
  Sequent(..),
  isTrivial,
  getSequent
) where

import Propositional.Prop
import Parser
import Data.List
import Control.Applicative
import Utils

-- [recognised variables]
data Sequent = [Prop] `Entails` Prop
             | [Prop] `Equivalent` Prop

instance Show Sequent where
  show :: Sequent -> String
  show (hypotheses `Entails` conclusion) =
    prettyArgs hypotheses ++ " ⊢ " ++ show conclusion
  show (hypothesis `Equivalent` conclusion) =
    show hypothesis ++ " ⟛ " ++ show conclusion

-- Evaluates if a sequent has been proven
-- by verifying that the conclusion has
-- been derived from the hypotheses
isTrivial :: Sequent -> Bool
isTrivial (as `Entails` c) = c `elem` as

sequentP :: Parser Sequent
sequentP = do l <- propP
              do symbol "|-" <|> symbol "⊢"
                 r <- propP
                 return ([l] `Entails` r)
               <|> do symbol "-||-" <|> symbol "⟛"
                      r <- propP
                      return ([] `Equivalent` r)
            <|> do ls <- list propP
                   symbol "|-" <|> symbol "⊢"
                   r <- propP
                   return (ls `Entails` r)
            <|> do symbol "|-" <|> symbol "⊢"
                   r <- propP
                   return ([] `Entails` r)

evalS :: String -> Either String Sequent
evalS = eval sequentP

getSequent :: IO Sequent
getSequent = do xs <- prompt "Input a sequent: "
                let s = evalS xs
                case s of
                  (Right s) -> return s
                  (Left errMsg) -> putStrLn errMsg >> getSequent