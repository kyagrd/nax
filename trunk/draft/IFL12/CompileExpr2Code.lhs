%include lhs2TeX.fmt
%include includelhs2tex.lhs



\begin{code}
{-# LANGUAGE  KindSignatures, TypeOperators  #-}
{-# LANGUAGE  GADTs, DataKinds, PolyKinds    #-}


module CompileExpr2Code where

data Ty = I | B   

data Val t where
  IV  :: Int  -> Val I
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
eval (VAL v)        = v
eval (PLUS e1 e2)   = plusV (eval e1) (eval e2)
eval (IF e0 e1 e2)  = ifV (eval e0) (eval e1) (eval e2)


data GList x i j where
  GNil   :: GList x i i
  GCons  :: x i j -> GList x j k -> GList x i k



append :: GList x i j -> GList x j k -> GList x i k
append GNil          ys  = ys
append (GCons x xs)  ys  = GCons x (append xs ys)


data Inst :: [Ty] -> [Ty] -> * where
  PUSH   :: Val t -> Inst ts (t .: ts)
  ADD    :: Inst (I .: I .: ts) (I .: ts)
  IFPOP  :: GList Inst ts ts' -> GList Inst ts ts' ->
            Inst (B .: ts) ts'




type Code sc sc' = GList Inst sc sc'

compile :: Expr t -> Code ts (t .: ts)
compile (VAL v) = GCons (PUSH v) GNil
         -- Does not type check without (|* : *|) extension.
         -- Error message from GHC 7.4.1:
         -- \quad    Couldn't match kind `|BOX|' against `|*|'
         -- \quad    Kind incompatibility when matching types:
         -- \quad\quad      |k0 :: BOX|
         -- \quad\quad      |[Ty] :: *|
         -- \quad    In the return type of a call of `|GCons|'
         -- \quad    In the expression: |GCons (PUSH v) GNil|
\end{code}
