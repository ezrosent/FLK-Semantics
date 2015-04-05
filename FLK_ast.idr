module FLK_ast

import Data.SortedMap

Ident : Type
Ident = String

data OpTy = Arith | Rel | Gen | Bool

data Op1 = Not | Fst | Snd

instance Show Op1 where
  show Not = "Not"
  show Fst = "Fst"
  show Snd = "Snd"

data Op2 : OpTy -> Type where
  Plus   : Op2 Arith
  Minus  : Op2 Arith
  LThan  : Op2 Rel
  LEThan : Op2 Rel
  GThan  : Op2 Rel
  GEThan : Op2 Rel
  EQ     : Op2 Gen
  NEQ    : Op2 Gen

instance Show (Op2 a) where
  show Plus = "+"
  show Minus = "-"
  show LThan = "<"
  show LEThan = "<="
  show GThan = ">"
  show GEThan = ">="
  show EQ = "="
  show NEQ = "!="

data Status = Inter | Done | Lam | RecLam

total
arithOp : Op2 Arith -> Nat -> Nat -> Nat
arithOp Plus  = (+)
arithOp Minus = (-)

total
relop : Op2 Rel -> Nat -> Nat -> Bool
relop LThan  = (<)
relop LEThan = (<=)
relop GThan  = (>)
relop GEThan = (>=)

-- Basic ADT for FLK
-- Status phantom type is used to tag useful subsets of the grammar

mutual
  Env : Type
  Env = SortedMap Ident (Exp Done `Either` Exp RecLam)

  data Exp : Status -> Type where
    Abs   : Ident   -> Exp a          -> Exp Lam
    Rec   : Ident   -> Exp a          -> Exp RecLam
    App   : Exp a   -> Exp b          -> Exp Inter
    If    : Exp a   -> Exp b -> Exp c -> Exp Inter
    Prim1 : Op1     -> Exp a          -> Exp Inter
    Prim2 : Op2 y   -> Exp a -> Exp b -> Exp Inter
    Id    : Ident                     -> Exp Inter
    N     : Nat                       -> Exp Done
    B     : Bool                      -> Exp Done
    Clos  : Env     -> Exp Lam        -> Exp Done
    Pair  : Exp a   -> Exp b          -> Exp Done

syntax "((" [exp] [e1] [e2] "))" = "("++exp++" "++(show e1)++" "++(show e2)++")";

instance Show (Exp a) where
  show (App x y) = (("" x y))
  show (Abs x y) = (("lambda" x y))
  show (Rec x y) = (("rec" x y))
  show (If x y z) = ((("if "++(show x)) y z))
  show (Prim1 x y) = (("" x y))
  show (Prim2 x z w) = (((show x) z w))
  show (N k) = (show k)
  show (B x) = (show x)
  show (Clos x y) = (("Clos" (map fst $ SortedMap.toList x) y))
  show (Id x) = (show x)
  show (Pair x y) = (("Pair" x y))


genOp : Op2 Gen -> Exp Done -> Exp Done -> Exp Done
genOp EQ (N k) (N j) = B (j == k)
genOp NEQ (N k) (N j) = B $ not (j == k)
genOp EQ (B y) (B x2) = B (y == x2)
genOp NEQ (B y) (B x2) = B $ not (y == x2)
genOp EQ a b = B False
genOp NEQ a b = B True

emptyEnv : Env
emptyEnv = empty
infixr 7 >-
data CF : Status -> Type where
  (>-) : {s : Status} -> (Exp s) -> Env -> (CF s)

instance Show (CF a) where
  show (x >- z) = "<" ++ show x ++ ", "++ (show $ map fst $ SortedMap.toList z)++ ">"

-- grab value from type
total
getTag : {b : Status} -> (state : Exp b) -> Status
getTag {b=b} _ = b

-- grab value from type with proof
total
getTagS : {b : Status} -> (state : Exp b) -> Sigma Status (\s => Sigma (Exp s) (\exp => exp = state))
getTagS {b=b} st = (b ** (st ** Refl))

-- grab value from type
total
getOpT : {b : OpTy} -> Op2 b -> OpTy
getOpT {b=b} _ = b
-- construct proof of containment with dependent pattern matching
idSteps :  (ident : Ident)
        -> (env : Env)
        -> Maybe (Sigma (Exp Done) (\v => lookup ident env = (Just (Left v))))
idSteps ident env with (lookup ident env)
  idSteps ident env | Nothing = Nothing
  idSteps ident env | (Just x) = h1 x ident env
where h1 : (x : Either (Exp Done) (Exp RecLam))
        -> String -> Env -> Maybe (Sigma (Exp Done) (\v => Just x = Just (Left v)))
      h1 (Left x) x1 x2 = Just (x ** Refl)
      h1 (Right x) x1 x2 = Nothing

-- construct proof of containment with dependent pattern matching
idRecSteps : (ident : Ident)
        -> (env : Env)
        -> Maybe (Sigma (Exp RecLam) (\v => lookup ident env = (Just (Right v))))
idRecSteps ident env with (lookup ident env)
  idRecSteps ident env | Nothing = Nothing
  idRecSteps ident env | (Just x) = h1 x ident env
where h1 : (x : Either (Exp Done) (Exp RecLam))
        -> String -> Env -> Maybe (Sigma (Exp RecLam) (\v => Just x = Just (Right v)))
      h1 (Left x) x1 x2 = Nothing
      h1 (Right x) x1 x2 = Just (x ** Refl)

yexpr : (Exp Inter)
yexpr = (App (App (Abs "f" (App (Abs "x" (App (Id "x") (Id "x"))) (Abs "g" (App (Id "f") (Abs "x" (App (App (Id "g") (Id "g")) (Id "x"))))))) (Abs "f" (Abs "n" (If (Prim2 EQ (Id "n") (N 0)) (N 0) (Prim2 Plus (Id "n") (App (Id "f") (Prim2 Minus (Id "n") (N 1)))))))) (N 4))

ycomb : (s ** CF s)
ycomb = (Inter ** yexpr >- emptyEnv)
