{-# LANGUAGE LambdaCase #-}
module Utils(
  prettyArgs,
  combine,
  prompt
) where

import Data.List
import System.Console.Haskeline

prettyArgs :: Show t => [t] -> String
prettyArgs [] = ""
prettyArgs ts = "(" ++ intercalate ", " (map show ts) ++ ")"

combine :: Eq a => [a] -> [a] -> [a]
combine xs ys = nub $ xs ++ ys

prompt :: String -> IO String
prompt text = runInputT defaultSettings $ do
  getInputLine text >>= \case
    Nothing   -> return ""
    Just line -> return line