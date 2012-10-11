{-# LANGUAGE KindSignatures, GADTs, DataKinds, PolyKinds #-}

-- list like thing in Conor's talk into Haskell!

data List x i j where
  Nil  :: List x i i
  Cons :: x i j -> List x j k -> List x i k

append :: List x i j -> List x j k -> List x i k
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)


-- instantiating to a length indexed list

data Nat = Z | S Nat

data VecR a i j where MkVecR :: a -> VecR a ('S i) i

type Vec a n = List (VecR a) n 'Z

vNil :: Vec a 'Z;
vNil = Nil

vCons :: a -> Vec a n -> Vec a ('S n)
vCons = Cons . MkVecR


-- instantiating to a plain list

data R a i j where MkR :: a -> R a '() '()

type PlainList a = List (R a) '() '()

nil :: PlainList a
nil = Nil

cons :: a -> PlainList a -> PlainList a
cons = Cons . MkR

