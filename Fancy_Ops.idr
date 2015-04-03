module Fancy_Ops
{- 
   This includes some work done on having more of a well-typed feel to the 
   Operational semantics for FLK. It wound up being farely complicated, and 
   ruined some of the untyped feel of the semantics, so now it is over here.  
 -}
import Data.SortedMap

Ident : Type
Ident = String

data Op2 : Type -> Type -> Type where
  Plus    : Op2 Nat Nat
  Minus   : Op2 Nat Nat
  Times   : Op2 Nat Nat
  LThan   : Op2 Nat Bool
  GThan   : Op2 Nat Bool
  LEThan  : Op2 Nat Bool
  GEThan  : Op2 Nat Bool
  EQual   : Op2 inT outT
  NEqual  : Op2 inT outT

data Op1 : Type -> Type -> Type where
  Not : Op1 Bool Bool

data Status = Inter | Done | Lam

mutual
  Env : Type
  Env = SortedMap Ident (Exp Done)

  data Exp : Status -> Type where
    App   : Exp a   -> Exp b          -> Exp Inter
    Abs   : Ident   -> Exp a          -> Exp Lam
    Rec   : Ident   -> Exp a          -> Exp Done
    If    : Exp a   -> Exp b -> Exp c -> Exp Inter
    Prim1 : Op1 w x -> Exp a          -> Exp Inter
    Prim2 : Op2 w x -> Exp a -> Exp b -> Exp Inter
    N     : Nat                       -> Exp Done
    B     : Bool                      -> Exp Done
    Clos  : Env     -> Exp Lam        -> Exp Done
    Id    : Ident                     -> Exp Inter

total
tView : (n : Exp Done) -> Type
tView (Rec _ _) = {a : Type} -> {b : Type} -> (a -> b)
tView (N _) = Nat
tView (B _) = Bool
tView (Clos _ _) = {a : Type} -> {b : Type} -> (a -> b)

total
calc1 : (x : Exp Done) -> (op : Op1 a b) -> (tView x = a) -> (y ** tView y = b)
calc1 (B x) Not prf = let b = B (not x) in (b ** Refl)
calc1 (Rec x y) Not prf = ?h7_1
calc1 (N k) Not prf = absurd (t prf)
  where t : (Nat = Bool) -> Void
calc1 (Clos x y) Not prf = ?h1_4


