module Propositional.Main (
  main
) where

import Propositional.Sequent
import Propositional.RuleApplication

main :: IO ()
main = do s <- getSequent
          case s of
            (_ `Entails` _) -> do res <- applyRule s
                                  putStrLn "Proof complete"
                                  return ()
            (a `Equivalent` c) -> do
              res1 <- applyRule ([a] `Entails` c)
              putStrLn "Forward sequent proven\n"
              res2 <- applyRule ([c] `Entails` a)
              putStrLn "Reverse sequent proven"
              putStrLn "Proof complete"
              return ()