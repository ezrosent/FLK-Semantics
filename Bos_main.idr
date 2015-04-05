module Main

import Data.SortedMap
import FLK_bos
import FLK_ast
import Effects
import Effect.StdIO


evalPrint : (s ** CF s) -> { [STDIO] } Eff ()
evalPrint (MkSigma x pf) with (evalCF x pf)
  evalPrint (MkSigma x pf) | Nothing = putStrLn $ "No evaluation for:" ++ (show pf)
  evalPrint (MkSigma x pf) | (Just (MkSigma y z)) = putStrLn $ (show pf) ++ " evaluates to " ++ (show y) ++ "by\n\t: " ++ (show z)

main : IO ()
main = do
  run $ evalPrint ycomb
  run $ evalPrint (Inter ** (Prim1 Fst (Pair (Prim2 Plus (N 2) (N 4)) (Prim1 Not (B False))) >- emptyEnv))
