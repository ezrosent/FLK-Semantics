module Main

import Data.SortedMap
import FLK_sos
import FLK_ast
import Effects
import Effect.StdIO

done : (s ** CF s) -> { [STDIO] } Eff (s ** CF s)
done (Done ** config) = do
  putStrLn $ "Finished with "++(show config)++" which is a value!"
  pure (Done ** config)
done (a ** config) = do
  putStrLn $ "Finished with "++(show config)++" which is stuck!"
  pure (a ** config)

transStr : (CF a) -> (CF b) -> (Step c d) -> String
transStr x x1 x2 =
  "Transitioning from:\n\t"++(show x)++"\n to \n\t"++(show x1)++"\n by rule ["++(show x2)++"]"

evalPrint : (s ** CF s) -> { [STDIO] } Eff (s' ** CF s')
evalPrint (MkSigma Inter pf) with (search pf)
  evalPrint (MkSigma Inter pf) | Nothing = done $ MkSigma Inter pf
  evalPrint (MkSigma Inter pf) | (Just (MkSigma x (MkSigma y z))) = do
    putStrLn $ transStr pf y z
    evalPrint $ MkSigma x y
evalPrint p@(MkSigma Done pf) = done p
evalPrint (MkSigma Lam pf) with (searchLam pf)
  evalPrint (MkSigma Lam pf) | Nothing = do done $ MkSigma Lam pf
  evalPrint (MkSigma Lam pf) | (Just (x ** (y ** z))) = do
    putStrLn $ transStr pf y z
    evalPrint $ MkSigma x y
evalPrint (MkSigma RecLam pf) = let (x ** (y ** z)) = recTrans pf in do
                                      putStrLn $ transStr pf y z
                                      evalPrint (x ** y)

runEval : Sigma Status (\s => (CF s)) -> IO (Sigma Status (\s' => CF s'))
runEval s = run $ evalPrint s

main : IO ()
main = do { runEval ycomb; pure ()}
  where example : (s ** CF s)
        example = (Inter ** (Prim2 Plus (Prim2 Plus (N 3) (N 4)) (B False)) >- emptyEnv)
        exp2 : Exp Inter
        exp2 = (App (Abs "x" (Prim2 Plus (N 4) (Id "x"))) (N 4))
        example2 : (s ** CF s)
        example2 = (Inter ** (exp2 >- emptyEnv))
