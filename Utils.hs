{-# LANGUAGE LambdaCase #-}

module Utils(
  prettyArgs,
  setPre,
  setApp,
  mergeSets,
  prompt
) where

import Data.List
import System.Console.Haskeline

prettyArgs :: Show t => [t] -> String
prettyArgs [] = ""
prettyArgs ts = "(" ++ intercalate ", " (map show ts) ++ ")"

setPre :: Eq a => a -> [a] -> [a]
setPre x xs = nub $ x : xs

setApp :: Eq a => a -> [a] -> [a]
setApp x xs = nub $ xs ++ [x]

mergeSets :: Eq a => [a] -> [a] -> [a]
mergeSets xs ys = nub $ xs ++ ys

prompt :: String -> IO String
prompt text = runInputT defaultSettings $ do
  getInputLine text >>= \case
    Nothing   -> return ""
    Just line -> return line