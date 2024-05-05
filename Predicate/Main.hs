module Predicate.Main (
  main
) where

import Predicate.Sequent
import Predicate.Symbol
import Predicate.RuleApplication

main :: IO ()
main = do sig <- getSymbols
          s <- getSequent sig
          case s of
            (_ `Entails` _) -> do res <- applyRule sig s
                                  putStrLn "Proof complete"
                                  return ()
            ((vs, a) `Equivalent` c) -> do
              res1 <- applyRule sig ((vs, [a]) `Entails` c)
              putStrLn "Forward sequent proven"
              res2 <- applyRule sig ((vs, [c]) `Entails` a)
              putStrLn "Reverse sequent proven"
              putStrLn "Proof complete"
              return ()