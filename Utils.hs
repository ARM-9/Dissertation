module Utils(
  prettyArgs,
  combine
) where

import Data.List

--
prettyArgs :: Show t => [t] -> String
prettyArgs [] = ""
prettyArgs ts = "(" ++ intercalate ", " (map show ts) ++ ")"

--
combine :: Eq a => [a] -> [a] -> [a]
combine xs ys = nub $ xs ++ ys
