module EnvLike where

open import Data.Nat
open import Data.Bool
open import Data.List


data Vec (a : Set) : ℕ -> Set where
  VNil  : {n : ℕ} -> Vec a n
  VCons : {n : ℕ} -> a -> Vec a n -> Vec a (suc n)

data Env {R} (iR : R -> Set) : {n : ℕ} -> Vec R n -> Set where
   Empty  : Env iR {0} VNil
   Extend : {r : R} {n : ℕ} {xs : Vec R n} ->
            iR r -> Env iR xs -> Env iR {suc n} (VCons r xs)

