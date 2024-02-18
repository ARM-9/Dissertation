{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Parser(
    Parser,
    parse,
    lower,
    upper,
    symbol,
    comma,
    list,
    eval
) where
    
import Control.Applicative
import Data.Char
import Control.Monad

newtype Parser a = P (String -> Either String (a, String))

parse :: Parser a -> String -> Either String (a, String)
parse (P p) = p

item :: Parser Char
item = P $ \input ->
  case input of
    []     -> Left "Empty input"
    (x:xs) -> Right (x, xs)

instance Functor Parser where
  fmap g p = P $ \input ->
    case parse p input of
      Left msg       -> Left msg
      Right (val, out) -> Right (g val, out)

instance Applicative Parser where
  pure v = P $ \input -> Right (v, input)

  pg <*> px = P $ \input ->
    case parse pg input of
      Left msg       -> Left msg
      Right (g, out) -> parse (fmap g px) out

instance Alternative Parser where
  empty = P $ \_ -> Left "Failed parse"

  p <|> q = P $ \input ->
    case parse p input of
      Left _         -> parse q input
      Right (val, out) -> Right (val, out)

instance Monad Parser where
  p >>= f = P $ \input ->
    case parse p input of
      Left msg       -> Left msg
      Right (val, out) -> parse (f val) out

instance MonadFail Parser where
  fail msg = P $ \_ -> Left msg

sat :: (Char -> Bool) -> Parser Char
sat predicate = do
  x <- item
  if predicate x then return x else fail $ "Unexpected character: " ++ [x]

lower :: Parser Char
lower = sat isLower

upper :: Parser Char
upper = sat isUpper

letter :: Parser Char
letter = sat isAlpha

alphanum :: Parser Char
alphanum = sat isAlphaNum

char :: Char -> Parser Char
char x = sat (== x)

string :: String -> Parser String
string = traverse char

space :: Parser ()
space = void $ many (sat isSpace)

token :: Parser a -> Parser a
token p = do space
             v <- p
             space
             return v

symbol :: String -> Parser String
symbol = token . string

comma :: Parser String
comma = symbol ","

list :: Parser a -> Parser [a]
list p = do x <- p
            xs <- many (comma >> p)
            return (x:xs)

eval :: Parser a -> String -> Either String a
eval p xs =
  case parse p xs of 
    Right (v, []) -> Right v
    Right (_, out) -> Left $ "Syntax error at " ++ show (length xs - length out)
    Left msg -> Left msg