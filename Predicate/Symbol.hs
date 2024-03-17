module Predicate.Symbol(
  Symbol(..),
  findSymbol,
  getSymbols
) where

import Parser
import Utils
import Control.Applicative

data Symbol = Constant String
            | Function String Int
            | Relation String Int
            deriving (Eq)

instance Show Symbol where
   show :: Symbol -> String
   show (Constant c) = c
   show (Function f n) = f ++ "(" ++ show n ++ ")"
   show (Relation r n) = r ++ "(" ++ show n ++ ")"

{-
  Accepts a String and list of Symbols and
  returns the first Symbol that matches the
  provided String or Nothing if no matching Symbol
  was found
-}
findSymbol :: String -> [Symbol] -> Maybe Symbol
findSymbol _ [] = Nothing
findSymbol xs (Constant sym : syms)
  | xs == sym = Just (Constant sym)
  | otherwise = findSymbol xs syms
findSymbol xs (Function sym arity : syms)
  | xs == sym = Just (Function sym arity)
  | otherwise = findSymbol xs syms
findSymbol xs (Relation sym arity : syms)
  | xs == sym = Just (Relation sym arity)
  | otherwise = findSymbol xs syms

arityP :: Parser Int
arityP = do symbol "("
            n <- countingNumber
            symbol ")"
            return n

symbolP :: [Symbol] -> Parser Symbol
symbolP syms = do r <- capitalisedStr
                  case findSymbol r syms of
                       Nothing -> Relation r <$> arityP
                       _       -> empty
              <|> do f <- lowerStr
                     case findSymbol f syms of
                          Nothing -> Function f <$> arityP
                          _       -> empty
              <|> do c <- lowerStr
                     case findSymbol c syms of
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

getSymbols :: IO [Symbol]
getSymbols = do xs <- prompt "Input a list of constant, function and relation symbols: "
                let s = evalSyms xs
                case s of
                  (Right s) -> return s
                  (Left errMsg) -> putStrLn errMsg >> getSymbols
