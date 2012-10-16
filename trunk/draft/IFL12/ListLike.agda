module ListLike where

open import Data.Nat; open import Data.Bool; open import Data.List

data Ty : Set where I : Ty; B : Ty

data Val : Ty -> Set where
  IV : ℕ -> Val I
  BV : Bool -> Val B

plusV : Val I -> Val I -> Val I
plusV (IV n) (IV m) = IV (n + m)

ifV : Val B -> {t : Ty} -> Val t -> Val t -> Val t
ifV (BV b) v1 v2 = if b then v1 else v2

data Expr : Ty -> Set where
  VAL  : {t : Ty} -> Val t -> Expr t
  PLUS : Expr I -> Expr I -> Expr I
  IF   : Expr B -> {t : Ty} -> Expr t -> Expr t -> Expr t


eval : {t : Ty} -> Expr t -> Val t
eval (VAL v)      = v
eval (PLUS e1 e2) = plusV (eval e1) (eval e2)
eval (IF e e1 e2) = ifV (eval e) (eval e1) (eval e2)


data GList {I : Set} (X : I -> I -> Set)
          : I -> I -> Set
  where
    GNil  : {i : I} -> GList X i i
    GCons : {i j k : I} -> X i j -> GList X j k -> GList X i k


append : {I : Set} -> {X : I -> I -> Set} -> {i j k : I} ->
         GList X i j -> GList X j k -> GList X i k
append GNil ys         = ys
append (GCons x xs) ys = GCons x (append xs ys) 


data Inst : List Ty -> List Ty -> Set where
  PUSH  : {t : Ty} {ts : List Ty} ->
          Val t -> Inst ts (t ∷ ts) 
  ADD   : {ts : List Ty } -> Inst (I ∷ I ∷ ts) (I ∷ ts)
  IFPOP : {ts ts' : List Ty} ->
          GList Inst ts ts' -> GList Inst ts ts' ->
          Inst (B ∷ ts) ts'

Code : List Ty -> List Ty -> Set
Code sc sc' = GList Inst sc sc'

compile : {t : Ty} -> {ts : List Ty} ->
          Expr t -> Code ts (t ∷ ts)
compile (VAL v)      = GCons (PUSH v) GNil
compile (PLUS e1 e2) = append (append (compile e1) (compile e2)) 
                              (GCons ADD GNil)
compile (IF e e1 e2) = append (compile e)
                              (GCons (IFPOP (compile e1)
                                            (compile e2))
                                     GNil)

{-
mutual 
 data Ev : Set where
  EO : Ev
  ES : Od -> Ev

 data Od : Set where
  OS : Ev -> Od

data Either (a : Set) (b : Set) : Set where
  Left  : a -> Either a b
  Right : b -> Either a b

case_of_ : {a b : Set} -> a -> (a -> b) -> b
case_of_ x f = f x

eoo : ℕ -> Either Ev Od
eoo 0 = Left EO
eoo (suc n) = case (eoo n) of λ{ (Left ev) -> Right(OS ev)
                                ; (Right od) -> Left(ES od) } 
-}
