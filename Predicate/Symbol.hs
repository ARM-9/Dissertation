module Predicate.Symbol(
  Symbol(..),
  getSym,
  evalSyms
) where

import Parser
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