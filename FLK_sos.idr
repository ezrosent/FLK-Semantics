module FLK_sos

import FLK_ast
import Data.SortedMap

-- operational semanitcs for FLK
-- TODO: Need way to have abstractions step
mutual
  infixr 5 >==> -- read like => in SOS-land
  (>==>) : (CF a) -> (CF b) -> Type
  l >==> r = Step l r

  syntax "[" [ex1] "=>" [ex2] "]"=
    ex1 >- _ `Step` ex2 >- _

  syntax "[" [ex1] "," [env1] "=>" [ex2] "," [env2] "]"=
    ex1 >- env1 `Step` ex2 >- env2

  data Step  : (CF a) -> (CF b) -> Type where
    PNot     :  [Prim1 Not (B b), e => B (not b),  e]

    PrimStep :  [b => b']
             -> [Prim1 o b, e => Prim1 o b', e]

    ArithOp  :  {o : Op2 Arith}
             -> [Prim2 o (N n1) (N n2), e => N (arithOp o n1 n2), e]

    RelOp    :  {o : Op2 Rel}
             -> [Prim2 o (N b1) (N b2), e => B (relop o b1 b2), e]

    GenOp    :  {o : Op2 Gen} -> {op1 : Exp Done} -> {op2 : Exp Done}
             -> [Prim2 o op1 op2, e => genOp o op1 op2, e]

    Prim2L   :  [b => b']
             -> [Prim2 o b re, e => Prim2 o b' re, e]

    Prim2R   :  {le : Exp Done}
             -> [b => b']
             -> [Prim2 o le b, e => Prim2 o le b', e]

    IfCase   :  [b => b']
             -> [If b t f, e' => If b' t f, e']

    IfT      :  [If (B True) t f, e => t, e]

    IfF      :  [If (B False) t f, e => f, e]

    ClosLam  :  [Abs ident exp, e => Clos e (Abs ident exp), e]

    AppFunT  :  [b => b']
             -> [App b exp, e => App b' exp, e]

    AppArgT  :  [arg => arg']
             -> [App (Clos env lam) arg, e => App (Clos env lam) arg', e]

    AppLam   :  {val : Exp Done}
             -> [App (Clos env (Abs ident body)) val, e => body, insert ident (Left val) env]

    IdTrans  :  {e : Env} -> {n : Ident}
             -> Sigma (Exp Done) (\v => lookup n e = (Just (Left v)))
             -> [(Id n), e => v, e]

    IdRecTrans :  {e : Env} -> {n : Ident}
              -> Sigma (Exp RecLam) (\v => lookup n e = (Just (Right v)))
              -> [(Id n), e => v, e]

    RecTrans :  [(Rec ident exp), e => exp, insert ident (Right $ Rec ident exp) e]

  syntax "[[" [str] "," [sub] "]]" = str++" ["++(show sub)++"]";

  instance Show (Step a b) where
    show PNot = "PNot"
    show (PrimStep w) = [["PrimStep", w]]
    show ArithOp = "ArithOp"
    show RelOp = "RelOp"
    show GenOp = "GenOp"
    show (Prim2L t) = [["Prim2L", t]]
    show (Prim2R s) = [["Prim2R", s]]
    show (IfCase s) = [["IfCase", s]]
    show IfT = "IfT"
    show IfF = "IfF"
    show ClosLam = "ClosLam"
    show (AppFunT s) = [["AppFunT", s]]
    show (AppArgT z) = [["AppArgT", z]]
    show AppLam = "AppLam"
    show (IdTrans x) = "IdTrans"
    show (IdRecTrans x) = "IdRecTrans"
    show RecTrans = "RecTrans"

-- Simple rule application
testStep1 : Prim1 Not (B True) >- e >==> (B False) >- e
testStep1 = PNot

-- Compose two rules
testStep : [(Prim1 Not (Prim1 Not (B False))), e => Prim1 Not (B True), e]
testStep {e=e} = PrimStep $ PNot {e=e}

takeStep : {state' : CF b} -> {rule : state >==> state'} -> (state : CF a) ->  CF b
takeStep {state' = s} _ = s

default : Exp a -> CF a
default x = x >- emptyEnv

opResolve : {e : Env}
         -> (op : Op2 a)
         -> (o1 : Exp Done)
         -> (o2 : Exp Done)
         -> Maybe (Sigma (Exp Done) (\state => Step ((Prim2 op o1 o2) >- e) (state >- e)))
opResolve EQ op1 op2 = Just ((genOp EQ op1 op2) ** GenOp)
opResolve NEQ op1 op2 = Just ((genOp NEQ op1 op2) ** GenOp)
opResolve Plus (N k) (N z) =  Just ((N $ arithOp Plus k z) ** ArithOp)
opResolve Minus (N k) (N z) = Just ((N $ arithOp Minus k z) ** ArithOp)
opResolve LThan (N k) (N z) =  Just ((B $ relop LThan k z) ** RelOp)
opResolve LEThan (N k) (N z) = Just ((B $ relop LEThan k z) ** RelOp)
opResolve GThan (N k) (N z) =  Just ((B $ relop GThan k z) ** RelOp)
opResolve GEThan (N k) (N z) =  Just ((B $ relop GEThan k z) ** RelOp)
opResolve x x1 x2 = Nothing


mutual
  -- Evaluator based on operational semantics
  -- TODO: add printing, with effects and such
  goTill : Sigma Status (\s => CF s) -> Sigma Status (\s' => CF s')
  goTill (MkSigma Inter pf) with (search pf)
    goTill (MkSigma Inter pf) | Nothing = MkSigma Inter pf
    goTill (MkSigma Inter pf) | (Just (MkSigma x (MkSigma y z))) = goTill $ MkSigma x y
  goTill p@(MkSigma Done pf) = p
  goTill (MkSigma Lam pf) with (searchLam pf)
    goTill (MkSigma Lam pf) | Nothing = (MkSigma Lam pf)
    goTill (MkSigma Lam pf) | (Just (MkSigma x (MkSigma y z))) = goTill $ MkSigma x y
  goTill (MkSigma RecLam pf) = let (x ** (y ** z)) = recTrans pf in goTill (x ** y)


  -- Search rules for the semantics
  -- Forall states, we get
  --      Maybe (exists a Status such that there exists a state with
  --            that status that is transitioned to by the state)
  search : (start : CF Inter) -> Maybe (Sigma Status (\s => (Sigma (CF s) (\o => Step start o))))
  search ((App z w) >- y)     = search_app y z w
  search ((If z w s) >- y)    = search_if z w s y
  search ((Prim1 z w) >- y)   = search_prim1 z w y
  search ((Prim2 z w s) >- y) = search_prim2 z w s y
  search ((Id x) >- y) with (idSteps x y)
    search ((Id x) >- y) | Nothing with (idRecSteps x y)
      search ((Id x) >- y) | Nothing | Nothing = Nothing
      search ((Id x) >- y) | Nothing | (Just (v ** pf)) =
        Just $ (RecLam ** (v >- y ** IdRecTrans (v ** pf)))
    search ((Id x) >- y) | Just (v ** pf) = Just $ (Done ** (v >- y ** IdTrans (v ** pf)))

  -- This is a macro that will do most of the intermediate computations needed for some common
  -- lemmas
  -- My understanding is that this sort of thing should be done with a high-level tactic
  -- involving reflection. I do not fully understand how to use this feature, so I am using the
  -- 'syntax' feature as a macro system of sorts
  syntax "[[" {state} "," {trans} "," [env] "," [ex] "," [newstate] "," [rule] "]]" =
               case (search $ ex >- env) of {
                 Nothing => Nothing ;
                 Just (status ** (state >- y' ** trans)) =>
                      Just (Inter ** (newstate >- env ** rule));
               }

  -- transition intermediate-result composite expressions. wrapper for above macro
  syntax "[[" [env] ";" [ex] ";" [newstate] ";" [rule] "]]" =
    [[ state, trans, env, ex, (newstate state), (rule trans)]]

  -- transition abstractions
  syntax "<[" [trans] "," [abs] "," [env] "," [state] "]>" =
    Just $ (_ ** (((state (Clos env abs)) >- env) ** trans ClosLam));
  -- transition rec expressions
  syntax "<[" [trans] ";" [rec] ";" [env] ";" [state] "]>" =
    let (tag ** (newstate >- env' ** newtrans)) = recTrans (rec >- env) in
        Just $ (_ ** ((state newstate) >- env ** trans newtrans));

  search_prim2_rhs_7 : (z : Op2 y)
                    -> (exp : Exp Done)
                    -> (s : Exp b)
                    -> (y : SortedMap String (Either (Exp Done) (Exp RecLam)))
                    -> Maybe (Sigma Status (\s2 => Sigma (CF s2)
                                   (\o => Step ((Prim2 z exp s) >- y) o)))
  search_prim2_rhs_7 z exp (App x w) y = [[y; (App x w); Prim2 z exp; Prim2R]]
  search_prim2_rhs_7 z exp (Abs x w) y = <[Prim2R, (Abs x w), y, Prim2 z exp]>
  search_prim2_rhs_7 z exp (Rec x w) y = <[Prim2R; (Rec x w); y; Prim2 z exp]>
  search_prim2_rhs_7 z exp (If x w s) y = [[y; If x w s; Prim2 z exp; Prim2R]]
  search_prim2_rhs_7 z exp (Prim1 x w) y = [[y; Prim1 x w; Prim2 z exp; Prim2R]]
  search_prim2_rhs_7 z exp (Prim2 w s t) y = [[y; Prim2 w s t; Prim2 z exp; Prim2R]]
  search_prim2_rhs_7 z exp (Id x) y = [[y; Id x; Prim2 z exp; Prim2R]]
  search_prim2_rhs_7 z exp (N k) y with (opResolve {e=y} z exp (N k))
    search_prim2_rhs_7 z exp (N k) y | Nothing = Nothing
    search_prim2_rhs_7 z exp (N k) y | (Just (exp ** step)) = Just (Done ** (exp >- y ** step))
  search_prim2_rhs_7 z exp (B x) y with (opResolve {e=y} z exp (B x))
    search_prim2_rhs_7 z exp (B x) y | Nothing = Nothing
    search_prim2_rhs_7 z exp (B x) y | (Just (exp ** step)) = Just (Done ** (exp >- y ** step))
  search_prim2_rhs_7 z exp (Clos x w) y with (opResolve {e=y} z exp (Clos x w))
    search_prim2_rhs_7 z exp (Clos x w) y | Nothing = Nothing
    search_prim2_rhs_7 z exp (Clos x w) y | (Just (exp ** step)) = Just (Done ** (exp >- y ** step))

  search_prim2 : (z : Op2 y)
              -> (w : Exp a)
              -> (s : Exp b)
              -> (y : SortedMap String (Either (Exp Done) (Exp RecLam)))
              -> Maybe (Sigma Status (\s1 => Sigma (CF s1)
                                             (\o => Step ((Prim2 z w s) >- y) o)))
  search_prim2 z (App x w) s y = [[y; (App x w); \st => Prim2 z st s; Prim2L]]
  search_prim2 z (Abs x w) s y = <[Prim2L, (Abs x w), y, \st => Prim2 z st s]>
  search_prim2 z (Rec x w) s y = <[Prim2L; (Rec x w); y; \st => Prim2 z st s]>
  search_prim2 z (If x w t) s y = [[y; If x w t; \st => Prim2 z st s; Prim2L]]
  search_prim2 z (Prim1 x w) s y = [[y; Prim1 x w; \st => Prim2 z st s; Prim2L]]
  search_prim2 z (Prim2 w t u) s y = [[y; Prim2 w t u; \st => Prim2 z st s; Prim2L]]
  search_prim2 z (Id x) s y = [[y; Id x; \st => Prim2 z st s; Prim2L]]
  search_prim2 z (N k) s y = search_prim2_rhs_7 z (N k) s y
  search_prim2 z (B x) s y = search_prim2_rhs_7 z (B x) s y
  search_prim2 z (Clos x w) s y = search_prim2_rhs_7 z (Clos x w) s y

  total
  searchLam : (start : CF Lam)
           -> Maybe (Sigma Status (\s => (Sigma (CF s) (\o => Step start o))))
  searchLam ((Abs x z) >- y) = <[ id , (Abs x z), y, id ]>

  total
  recTrans : (start : CF RecLam)
          -> (Sigma Status (\s => (Sigma (CF s) (\o => Step start o))))
  recTrans ((Rec x z) >- y) = (getTag z ** (z >- (insert x (Right $ Rec x z) y) ** RecTrans))


  total
  searchRec : (start : CF RecLam)
           -> Maybe (Sigma Status (\s => (Sigma (CF s) (\o => Step start o))))
  searchRec r = Just $ recTrans r

  search_if : (z : Exp a)
           -> (w : Exp b)
           -> (s : Exp c)
           -> (y : Env)
           -> Maybe (Sigma Status (\s1 => Sigma (CF s1) (\o => Step ((If z w s) >- y) o)))
  search_if (Abs x z) w s y  = <[IfCase, (Abs x z), y, \c => If c w s]> --Nothing
  search_if (Rec i b) w s y  = <[IfCase; (Rec i b); y; \c => If c w s]>
  search_if (N _) _ _ _      = Nothing
  search_if (Clos _ _) _ _ _ = Nothing
  search_if (B x) w s y = case x of
                               True  => let t = getTag w in
                                            Just (t ** (w >- y ** IfT))
                               False => let t = getTag s in
                                            Just (t ** (s >- y ** IfF))
  search_if (App lam st)  w s y = [[state, trans, y, App lam st, If state w s , IfCase trans]]
  search_if (If x z t)    w s y = [[y; (If x z t); \state => If state w s; IfCase]]
  search_if (Prim1 x z)   w s y = [[y; (Prim1 x z); \state => If state w s; IfCase]]
  search_if (Prim2 x z t) w s y = [[y; (Prim2 x z t); \state => If state w s; IfCase]]
  search_if (Id x)        w s y = [[y; (Id x); \state => If state w s; IfCase]]

  search_prim1 : (z : Op1)
              -> (w : Exp a)
              -> (y : Env)
              -> Maybe (Sigma Status (\s => Sigma (CF s) (\o => Step ((Prim1 z w) >- y) o)))
  search_prim1 Not (Abs x z)  y = <[PrimStep, (Abs x z), y, (Prim1 Not)]>
  search_prim1 Not (Rec x z)  y = <[PrimStep; (Rec x z); y; (Prim1 Not)]>
  search_prim1 Not (N k)      y = Nothing
  search_prim1 Not (Clos x z) y = Nothing
  search_prim1 Not (B x) y = Just $ (Done ** (B (not x) >- y ** PNot))
  search_prim1 Not (App x z)     y = [[y; (App x z); Prim1 Not; PrimStep]]
  search_prim1 Not (If x z w)    y = [[y; (If x z w); Prim1 Not; PrimStep]]
  search_prim1 Not (Prim1 x z)   y = [[y; (Prim1 x z); Prim1 Not; PrimStep]]
  search_prim1 Not (Prim2 z w s) y = [[y; (Prim2 z w s); Prim1 Not; PrimStep]]
  search_prim1 Not (Id x)        y = [[y; (Id x); Prim1 Not; PrimStep]]

  search_subst_env : (y : Env) -- Outer environment
                  -> (x : Env) -- Closure environment
                  -> (z : Exp Lam)
                  -> (k : Exp Done)
                  -> Maybe (Sigma Status
                                 (\s => Sigma (CF s)
                                              (\o => Step ((App (Clos x z) k) >- y) o)))
  search_subst_env y x (Abs iden w) k =
    Just $ (getTag w ** (w >- (insert iden (Left k) x) ** AppLam))

  search_app : (y : Env)
            -> (z : Exp a)
            -> (w : Exp b)
            -> Maybe (Sigma Status (\s => Sigma (CF s) (\o => Step ((App z w) >- y) o)))
  search_app y p@(Abs id body) w  = <[AppFunT, (Abs id body), y, (\clos => App clos w)]>
  search_app y (App e b)        w = [[y; (App e b); \s => App s w; AppFunT]]
  search_app y (If c t f)       w = [[y; (If c t f); \s => App s w; AppFunT]]
  search_app y (Prim1 op oa)    w = [[y; (Prim1 op oa); \s => App s w; AppFunT]]
  search_app y (Prim2 op o1 o2) w = [[y; (Prim2 op o1 o2); \s => App s w; AppFunT]]
  search_app y (Id x)           w = [[y; (Id x); \s => App s w; AppFunT]]
  search_app y (N k)            w = Nothing
  search_app y (B x)            w = Nothing
  search_app y (Rec x z)        w   = <[AppFunT; (Rec x z); y; (\clos => App clos w)]>
  search_app y (Clos x z) (Rec w s) = <[AppArgT; (Rec w s); y; (\arg => App (Clos x z) arg)]>
  search_app y (Clos x z) (App e b)        = [[y; App e b; App (Clos x z); AppArgT]]
  search_app y (Clos x z) (If c t f)       = [[y; If c t f; App (Clos x z); AppArgT]]
  search_app y (Clos x z) (Prim1 op oa)    = [[y; Prim1 op oa; App (Clos x z); AppArgT]]
  search_app y (Clos x z) (Prim2 op o1 o2) = [[y; Prim2 op o1 o2; App (Clos x z); AppArgT]]
  search_app y (Clos x z) (Id i)           = [[y; Id i; App (Clos x z); AppArgT]]
  search_app y (Clos x z) p@(Abs _ _)      = Just $ (Inter **
                                                     (App (Clos x z) (Clos y p) >- y **
                                                       AppArgT ClosLam))
  search_app y (Clos x z) p@(N k)          = search_subst_env y x z p
  search_app y (Clos x z) p@(B w)          = search_subst_env y x z p
  search_app y (Clos x z) p@(Clos w s)     = search_subst_env y x z p
