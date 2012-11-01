{-# LANGUAGE KindSignatures, GADTs, DataKinds, PolyKinds, TypeOperators #-}





{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{DataKinds},\;\texttt{KindSignatures}} }"-}

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
   \textcolor{gray}{\texttt{+}\;\texttt{DataKinds},\;\texttt{PolyKinds}} \qquad}"-}

{-""-}
{-""-}
data Path x i j where
  PNil   :: Path x i i
  PCons  :: x i j  -> Path x j k
                   -> Path x i k

{-""-}
append :: Path x i j  -> Path x j k
                      -> Path x i k
append PNil            ys  = ys
append (  PCons x xs)  ys  =
          PCons x (append xs ys)






{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{GADTs},\;\texttt{DataKinds},\;\texttt{PolyKinds}} }"-}
data List a = Nil | a :. List a{-"~"-};{-"~"-}infixr :.
data Inst :: List Ty -> List Ty -> * where
  PUSH   :: Val t -> Inst ts (t :. ts)
  ADD    :: Inst (I :. I :. ts) (I :. ts)
  IFPOP  :: Path Inst ts ts' ->
            Path Inst ts ts' ->
            Inst (B :. ts) ts'
{-""-}
{-""-}
{-""-}

type Code sc sc' = Path Inst sc sc'

{-""-}
compile :: Expr t -> Code ts (t :. ts)
compile (VAL v) =
  PCons (PUSH v) PNil
compile (PLUS e1 e2) =
  append  (append  (compile e1) (compile e2)) 
          (PCons ADD PNil)
compile (IF e0 e1 e2) =
  append  (compile e0)
          (PCons  (IFPOP  (compile e1)
                          (compile e2))
                  PNil)





-- instantiating to a plain regular list

data Elem a i j where
  MkElem :: a -> Elem a () ()

type List' a = Path (Elem a) () ()

nil' = PNil {-"~"-} :: List' a

cons' :: a -> List' a -> List' a
cons' = PCons . MkElem

-- instantiating to a length indexed list

data Nat = Z | S Nat

data ElemV a i j where
  MkElemV :: a -> ElemV a (S n) n

type Vec a n = Path (ElemV a) n Z

vNil = PNil {-"~"-} :: Vec a Z

vCons :: a -> Vec a n -> Vec a (S n)
vCons = PCons . MkElemV

