\begin{code}
module Env where

open import Data.Nat

data Vec (a : Set) : ℕ -> Set where
  VNil  : {n : ℕ} -> Vec a n
  VCons : {n : ℕ} -> a -> Vec a n -> Vec a (suc n)

data Env {R} (iR : R -> Set) : {n : ℕ} -> Vec R n -> Set where
   Empty  : Env iR {0} VNil
   Extend : {r : R} {n : ℕ} {xs : Vec R n} ->
            (res : iR r) -> Env iR xs -> Env iR {suc n} (VCons r xs)
\end{code}