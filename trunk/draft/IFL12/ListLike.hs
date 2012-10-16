{-# LANGUAGE KindSignatures, GADTs, DataKinds, PolyKinds, TypeOperators #-}

data Ty = I | B

data Val t where
  IV  :: Int -> Val I
  BV  :: Bool -> Val B

plusV :: Val I -> Val I -> Val I
plusV (IV n) (IV m) = IV (n + m)

ifV :: Val B -> Val t -> Val t -> Val t
ifV (BV b) v1 v2 = if b then v1 else v2

data Expr t where
  VAL   :: Val t -> Expr t
  PLUS  :: Expr I -> Expr I -> Expr I
  IF    :: Expr B -> Expr t -> Expr t -> Expr t

eval :: Expr t -> Val t
eval (VAL v) = v
eval (PLUS e1 e2) = plusV (eval e1) (eval e2)
eval (IF e e1 e2) = ifV (eval e) (eval e1) (eval e2)

data GList x i j where
  Nil  :: GList x i i
  Cons :: x i j -> GList x j k -> GList x i k

data Inst :: [Ty] -> [Ty] -> * where
  PUSH  :: Val t -> Inst ts (t ': ts)
  ADD   :: Inst (I ': I ': ts) (I ': ts)
  IFPOP :: GList Inst ts ts' -> GList Inst ts ts' -> Inst (B ': ts) ts'

compile :: Expr t -> GList Inst ts (t ': ts)
compile (VAL v) = undefined -- Cons (PUSH v) Nil -- does not type check without (*:*)
{- GListLike.hs:35:19:
 -     Couldn't match kind `BOX' against `*'
 -     Kind incompatibility when matching types:
 -       k0 :: BOX
 -       [Ty] :: *
 -     In the return type of a call of `Cons'
 -     In the expression: Cons (PUSH v) Nil
 -}


-- list like thing in Conor's talk into Haskell!


append :: GList x i j -> GList x j k -> GList x i k
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)


-- instantiating to a length indexed list

data Nat = Z | S Nat

data VecR a i j where MkVecR :: a -> VecR a (S i) i

type Vec a n = GList (VecR a) n Z

vNil :: Vec a Z
vNil = Nil

vCons :: a -> Vec a n -> Vec a (S n)
vCons = Cons . MkVecR


-- instantiating to a plain list

data R a i j where MkR :: a -> R a () ()

type List a = GList (R a) () ()

nil :: List a
nil = Nil

cons :: a -> List a -> List a
cons = Cons . MkR

