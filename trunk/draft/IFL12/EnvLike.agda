module EnvLike where

open import Data.Nat
open import Data.Bool
open import Data.List




data Vec (a : Set) : ℕ -> Set where
  VNil   : {n : ℕ} -> Vec a n
  VCons  : {n : ℕ} -> a -> Vec a n -> Vec a (suc n)

data Env {st} (res : st -> Set) : {n : ℕ} -> Vec st n -> Set where
   Empty   : Env res {0} VNil
   Extend  : {n : ℕ} {x : st} {xs : Vec st n} ->
             res x -> Env res xs -> Env res {suc n} (VCons x xs)

