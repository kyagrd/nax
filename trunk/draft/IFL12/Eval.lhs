%include lhs2TeX.fmt
%include includelhs2tex.lhs

\begin{code}
{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{GADTs},\;\texttt{DataKind},\;\texttt{PolyKind}} }"-}

data Ty = I | B   
{-""-}

data Val t where
  IV  :: Int  -> Val I
  BV  :: Bool -> Val B

plusV :: Val I -> Val I -> Val I
plusV (IV n) (IV m) = IV (n + m)

ifV :: Val B -> Val t -> Val t -> Val t
ifV (BV b) v1 v2 = if b then v1 else v2

{-""-}

data Expr t where
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
\end{code}
