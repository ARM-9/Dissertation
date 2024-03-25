module Propositional.Main (
  main
) where

import Propositional.Sequent
import Propositional.RuleApplication

main :: IO ()
main = do s <- getSequent
          case s of
            (_ `Entails` _) -> do res <- applyRule s
                                  print res
                                  return ()
            (a `Equivalent` c) -> do
              res1 <- applyRule ([a] `Entails` c)
              res2 <- applyRule ([c] `Entails` a)
              print $ res1 && res2
              return ()