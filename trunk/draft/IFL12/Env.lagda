\begin{code}
module Env where

open import Data.Nat
open import Data.Bool

data Vec (a : Set) : ℕ -> Set where
  VNil  : {n : ℕ} -> Vec a n
  VCons : {n : ℕ} -> a -> Vec a n -> Vec a (suc n) 

data Bool1 : Set1 where true1 false1 : Bool1

data Env {tyR : Set} (iR : tyR -> Set) : {n : ℕ} -> Vec tyR n -> Set where
   Empty  : Env  iR {0} VNil
   Extend : {r : tyR} {n : ℕ} {xs : Vec tyR n} ->
            (res : iR r) -> Env iR xs -> Env iR {suc n} (VCons r xs)
\end{code}