module Predicate.Main(
  main
) where
import Predicate.Sequent
import Predicate.Symbol
import Predicate.RuleApplication

main :: IO ()
main = do syms <- getSymbols "Input a list of constant, function and relation symbols: "
          s <- getSequent syms "Input a sequent: "
          case s of
            (_ `Entails` _) -> do res <- applyRule'' syms s
                                  print res
                                  return ()
            ((vs, a) `Biconditional` c) -> do
              res1 <- applyRule'' syms ((vs, [a]) `Entails` c)
              res2 <- applyRule'' syms ((vs, [c]) `Entails` a)
              print $ res1 && res2
              return ()