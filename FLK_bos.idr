module FLK_bos

import FLK_ast


mutual
  syntax "[" [ex1] "=>>" [ex2] "]" =
      ex1 >- _ `BigStep` ex2 >- _

  syntax "[" [ex1] "," [env1] "=>>" [ex2] "," [env2] "]" =
      ex1 >- env1 `BigStep` ex2 >- env2

  -- Big Step rules for FLK
  data BigStep : (CF a) -> (CF Done) -> Type where
    DoneEv : {d : Exp Done} -> [d, e =>> d, e]

    FstEv   : [e1 =>> (Pair eFst eSnd)]
           -> [eFst =>> v1]
           -> [Prim1 Fst e1, env =>> v1, env']

    SndEv   : [e1 =>> (Pair eFst eSnd)]
           -> [eSnd =>> v1]
           -> [Prim1 Snd e1, env =>> v1, env']

    Prim1Ev : [e =>> (B b)]
           -> [Prim1 Not e, env =>> B (not b), env]

    Prim2NEv : [e1 =>> (N n1)]
            -> [e2 =>> (N n2)]
            -> [(Prim2 o e1 e2), env =>> (N (arithOp o n1 n2)), env]

    Prim2REv : [e1 =>> (N n1)]
            -> [e2 =>> (N n2)]
            -> [(Prim2 o e1 e2), env =>> (B (relop o n1 n2)), env]

    Prim2Gen : {v1 : Exp Done} -> {v2 : Exp Done}
            -> [e1 =>> v1]
            -> [e2 =>> v2]
            -> [(Prim2 o e1 e2), env =>> genOp o v1 v2, env]

    IfTEv : [cond =>> (B True)]
         -> [t =>> v]
         -> [If cond t f, e =>> v, e]

    IfFEv : [cond =>> (B False)]
         -> [f =>> v]
         -> [If cond t f, e =>> v, e]

    IdValEv : {ident : Ident} -> {e : Env}
           -> Sigma (Exp Done) (\st => lookup ident e = Just (Left st))
           -> [Id ident, e =>> v, e']

    IdRecEv : {ident : Ident} -> {e : Env}
           -> Sigma (Exp RecLam) (\st => lookup ident e = Just (Right st))
           -> [v, e =>> r, e']
           -> [Id ident, e =>> r, e']

    LamEv : [Abs x body, env =>> Clos env (Abs x body), env]

    RecEv : {env : Env} -> {ident : Ident} -> {body : Exp a}
         -> [body, (insert ident (Right $ Rec ident body) env) =>> v, env']
         -> [Rec ident body, env =>> v, env']

    AppEv : [func =>> (Clos e (Abs ident body))]
         -> [arg =>> argval]
         -> [body, (insert ident (Left $ argval) e) =>> v,e']
         -> [App func arg, e'' =>> v,e']

  instance Show (BigStep a b) where
    show DoneEv = "DoneEv"
    show (Prim1Ev z) = (show z) ++ " -> PrimEv"
    show (Prim2NEv w u) = (show w) ++ " and " ++ (show u) ++ " -> " ++ "Prim2NEv"
    show (Prim2REv w u) = (show w) ++ " and " ++ (show u) ++ " -> " ++ "Prim2REv"
    show (Prim2Gen w u) = (show w) ++ " and " ++ (show u) ++ " -> " ++ "Prim2GEv"
    show (IfTEv w x1) = (show w) ++ " and " ++ (show x1) ++ " -> " ++ "IfTEv"
    show (IfFEv w x1) = (show w) ++ " and " ++ (show x1) ++ " -> " ++ "IfFEv"
    show (IdValEv y) = "IdValEv"
    show (IdRecEv x y) = (show y) ++ " -> IdRecEv"
    show LamEv = "LamEv"
    show (RecEv x) = (show x) ++ "-> RecEv"
    show (AppEv s x1 y1) = (show s) ++ " and " ++ (show x1) ++ " and " ++ (show y1) ++ " -> " ++ "AppEv"
    show (FstEv p1 p2) = (show p1) ++ " and " ++ (show p1) ++ " -> " ++ "FstEv"
    show (SndEv p1 p2) = (show p1) ++ " and " ++ (show p1) ++ " -> " ++ "SndEv"

  transStr : (CF a) -> (CF b) -> String
  transStr c d = "["++(show c)++"] =>> ["++(show d)++"]"

prim2Lemma : (ot : OpTy) -> (op : Op2 ot) -> (e1 : Exp Done) -> (e2 : Exp Done)
          -> (tr1 : [e1' =>> e1]) -> (tr2 : [e2' =>> e2])
          -> (env : Env)
          -> Maybe (Sigma (CF Done) (\res => Prim2 op e1' e2' >- env `BigStep` res))
prim2Lemma Arith op (N k) (N j) tr1 tr2 y =
  Just ((N $ arithOp op k j) >- y ** Prim2NEv tr1 tr2)
prim2Lemma Arith op e1 e2 tr1 tr2 y = Nothing
prim2Lemma Rel op (N k) (N j) tr1 tr2 y =
  Just ((B $ relop op k j) >- y ** Prim2REv tr1 tr2)
prim2Lemma Rel op e1 e2 tr1 tr2 y = Nothing
prim2Lemma Gen op e1 e2 tr1 tr2 y = Just ((genOp op e1 e2) >- y ** Prim2Gen tr1 tr2)
prim2Lemma Bool op e1 e2 tr1 tr2 y = Nothing

mutual
  syntax "[[" [exp] "," [env] "]]" = evalCF (getTag exp) (exp >- env);

  evalCFI : (st : CF Inter) -> Maybe (Sigma (CF Done) (\st' => st `BigStep` st'))
  evalCFI ((App x z) >- y) = do
    ((stateF >- yF) ** transF) <- [[x, y]]
    ((stateA >- yA) ** transA) <- [[z, y]]
    case stateF of
         (Clos env (Abs ident body)) => do
           ((stateRes >- yRes) ** transRes) <- [[body, (insert ident (Left $ stateA) env)]]
           pure $ ((stateRes >- yRes) ** AppEv transF transA transRes)
         otherwise => Nothing

  evalCFI ((If x z w) >- y) = do
    ((stateC >- _) ** transC) <- [[x, y]]
    case stateC of
         (B False) => do
           ((stateF >- _) ** transF) <- [[w, y]]
           pure (stateF >- y ** (IfFEv transC transF))
         (B True)  => do
           ((stateT >- _) ** transT) <- [[z, y]]
           pure (stateT >- y ** (IfTEv transC transT))
         otherwise => Nothing

  evalCFI ((Prim1 Not z) >- y) = do
    ((state >- _) ** trans') <- [[z, y]]
    case state of
         (B b) => pure ((B $ not b) >- y ** (Prim1Ev trans'))
         otherwise => Nothing

  evalCFI ((Prim1 Fst z) >- y) = do
    ((state >- _) ** trans) <- [[z, y]]
    case state of
         (Pair e1 e2) =>  do
           ((state' >- y') ** trans') <- [[e1, y]]
           pure $ ((state' >- y') ** FstEv trans trans')
         otherwise => Nothing

  evalCFI ((Prim1 Snd z) >- y) = do
    ((state >- _) ** trans) <- [[z, y]]
    case state of
         (Pair e1 e2) =>  do
           ((state' >- y') ** trans') <- [[e2, y]]
           pure $ ((state' >- y') ** SndEv trans trans')
         otherwise => Nothing

  evalCFI ((Prim2 z w s) >- y) = do
    ((st1 >- _) ** tr1) <- [[w, y]]
    ((st2 >- _) ** tr2) <- [[s, y]]
    prim2Lemma (getOpT z) z st1 st2 tr1 tr2 y


  evalCFI ((Id x) >- y) with (idSteps x y)
    evalCFI ((Id x) >- y) | (Just (MkSigma z pf)) = do {
        ((st >- y') ** trans) <- [[z, y]];
        pure $ ((st >- y') ** (IdValEv (MkSigma z pf)))
      }
    evalCFI ((Id x) >- y) | Nothing with (idRecSteps x y)
      evalCFI ((Id x) >- y) | Nothing | Nothing = Nothing
      evalCFI ((Id x) >- y) | Nothing | (Just (MkSigma z pf)) = do {
        ((st >- y') ** trans) <- [[z, y]];
        pure $ ((st >- y') ** (IdRecEv (MkSigma z pf) trans))
      }

  evalCFD : (st : CF Done) -> (Sigma (CF Done) (\st' => st `BigStep` st'))
  evalCFD (x >- z) = (x >- z ** DoneEv)

  evalCFL : (st : CF Lam) -> (Sigma (CF Done) (\st' => st `BigStep` st'))
  evalCFL ((Abs x z) >- y) = ((Clos y (Abs x z)) >- y ** LamEv)

  evalCFR : (st : CF RecLam) -> Maybe (Sigma (CF Done) (\st' => st `BigStep` st'))
  evalCFR ((Rec x z) >- y) = do
    ((stateN >- y') ** transN) <- [[z, (insert x (Right $ Rec x z) y)]]
    pure (stateN >- y' ** RecEv transN)

  evalCF : (s : Status) -> (st : CF s) -> Maybe (Sigma (CF Done) (\st' => st `BigStep` st'))
  evalCF Inter st = evalCFI st
  evalCF Done st = Just $ evalCFD st
  evalCF Lam st = Just $ evalCFL st
  evalCF RecLam st = evalCFR st

evalErase : (Exp s) -> Maybe (CF Done)
evalErase x = [[x, emptyEnv]] >>= (\ (cf ** _) => pure cf)


