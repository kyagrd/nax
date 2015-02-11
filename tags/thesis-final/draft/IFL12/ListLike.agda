module ListLike where

open import Data.Nat
open import Data.Bool
open import Data.List





{-"\underline{\textsc{Agda}_{\phantom{g}}
              \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad}"-}

data Ty : Set where  I : Ty
                     B : Ty 

data Val : Ty -> Set where
  IV  : ℕ    -> Val I
  BV  : Bool -> Val B

plusV : Val I -> Val I -> Val I
plusV (IV n) (IV m) = IV (n + m)

ifV : Val B -> {t : Ty} -> Val t -> Val t -> Val t
ifV (BV b) v1 v2 = if b then v1 else v2

{-""-}

data Expr : Ty -> Set where
  VAL   : {t : Ty} -> Val t -> Expr t
  PLUS  : Expr I -> Expr I -> Expr I
  IF    : Expr B ->
          {t : Ty} -> Expr t -> Expr t -> Expr t
{-""-}
eval : {t : Ty} -> Expr t -> Val t
eval (VAL v)        = v
eval (PLUS e1 e2)   =
  plusV  (eval e1) (eval e2)
eval (IF e0 e1 e2)  =
  ifV (eval e0) (eval e1) (eval e2)





{-"\underline{\textsc{Agda}_{\phantom{g}}^{\phantom{A^k}}
              \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\quad~~} "-}
{-""-}
data Path {Ix : Set} (X : Ix -> Ix -> Set) : Ix -> Ix -> Set
  where
    PNil   : {i : Ix} -> Path X i i
    PCons  : {i j k : Ix} ->
             X i j -> Path X j k -> Path X i k

{-""-}

append : {Ix : Set} -> {X : Ix -> Ix -> Set} -> {i j k : Ix}
  {-"~~"-} -> Path X i j -> Path X j k -> Path X i k
append  PNil          ys  = ys
append  (PCons x xs)  ys  =
        {-"~"-}PCons x (append xs ys) 






{-"\underline{\textsc{Agda}_{\phantom{g}}
              \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad}"-}

data Inst : List Ty -> List Ty -> Set where
  PUSH   : {t : Ty} {ts : List Ty} ->
           Val t -> Inst ts (t ∷ ts) 
  ADD    : {ts : List Ty } ->
           Inst (I ∷ I ∷ ts) (I ∷ ts)
  IFPOP  : {ts ts' : List Ty} ->
           Path Inst ts ts' ->
           Path Inst ts ts' ->
           Inst (B ∷ ts) ts'

Code : List Ty -> List Ty -> Set
Code sc sc' = Path Inst sc sc'

compile  : {t : Ty} -> {ts : List Ty} ->
           Expr t -> Code ts (t ∷ ts)
compile (VAL v)       =
  PCons (PUSH v) PNil
compile (PLUS e1 e2)  =
  append  (append  (compile e1) (compile e2)) 
          (PCons ADD PNil)
compile (IF e0 e1 e2)  =
  append  (compile e0)
          (PCons  (IFPOP  (compile e1)
                          (compile e2))
                  PNil)





-- instantiating to a plain regular list 

record Unit : Set where constructor <>

List' : Set -> Set
List' a = Path (λ i j -> a) <> <>
 
nil' : {a : Set} -> List' a
nil' = PNil

cons' : {a : Set} -> a -> List' a -> List' a
cons' = PCons

-- instantiating to a length indexed list

Vec : Set -> ℕ -> Set
Vec a n = Path (λ i j -> a) n zero

vNil : {a : Set} -> Vec a zero
vNil = PNil

vCons  : {a : Set} {n : ℕ} ->
         a -> Vec a n -> Vec a (suc n)
vCons = PCons

