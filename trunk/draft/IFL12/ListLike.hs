{-# LANGUAGE KindSignatures, GADTs, DataKinds, PolyKinds, TypeOperators #-}





{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{DataKind},\;\texttt{KindSignatures}} }"-}

data Ty = I | B   
{-""-}

data Val :: Ty -> * where
  IV  :: Int  -> Val I
  BV  :: Bool -> Val B

plusV :: Val I -> Val I -> Val I
plusV (IV n) (IV m) = IV (n + m)

ifV :: Val B -> Val t -> Val t -> Val t
ifV (BV b) v1 v2 = if b then v1 else v2

{-""-}

data Expr :: Ty -> * where
  VAL   :: Val t -> Expr t
  PLUS  :: Expr I -> Expr I -> Expr I
  IF    :: Expr B ->
           Expr t -> Expr t -> Expr t

eval :: Expr t -> Val t
eval (VAL v)        = v
eval (PLUS e1 e2)   =
  plusV  (eval e1) (eval e2)
eval (IF e0 e1 e2)  =
  ifV  (eval e0) (eval e1) (eval e2)





{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{GADTs},\;\texttt{DataKind},\;\texttt{PolyKind}} }"-}

{-""-}
{-""-}
data GList x i j where
  GNil   :: GList x i i
  GCons  :: x i j  -> GList x j k
                   -> GList x i k

{-""-}
append :: GList x i j  -> GList x j k
                       -> GList x i k
append GNil            ys  = ys
append (  GCons x xs)  ys  =
          GCons x (append xs ys)






{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{GADTs},\;\texttt{DataKind},\;\texttt{PolyKind}} }"-}
data List a = Nil | a :. List a{-"~"-};{-"~"-}infixr :.
data Inst :: List Ty -> List Ty -> * where
  PUSH   :: Val t -> Inst ts (t :. ts)
  ADD    :: Inst (I :. I :. ts) (I :. ts)
  IFPOP  :: GList Inst ts ts' ->
            GList Inst ts ts' ->
            Inst (B :. ts) ts'
{-""-}
{-""-}
{-""-}

type Code sc sc' = GList Inst sc sc'

{-""-}
compile :: Expr t -> Code ts (t :. ts)
compile (VAL v) =
  GCons (PUSH v) GNil
compile (PLUS e1 e2) =
  append  (append  (compile e1) (compile e2)) 
          (GCons ADD GNil)
compile (IF e e1 e2) =
  append  (compile e)
          (GCons  (IFPOP  (compile e1)
                          (compile e2))
                  GNil)





-- instantiating to a plain regular list

data Elem a i j where
  MkElem :: a -> Elem a () ()

type List' a = GList (Elem a) () ()

nil' = GNil {-"~"-} :: List' a

cons' :: a -> List' a -> List' a
cons' = GCons . MkElem

-- instantiating to a length indexed list

data Nat = Z | S Nat

data ElemV a i j where
  MkElemV :: a -> ElemV a (S n) n

type Vec a n = GList (ElemV a) n Z

vNil = GNil {-"~"-} :: Vec a Z

vCons :: a -> Vec a n -> Vec a (S n)
vCons = GCons . MkElemV

