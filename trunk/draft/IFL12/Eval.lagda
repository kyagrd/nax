%include lhs2TeX.fmt
%include agda.fmt
%include includelhs2tex.lhs
\begin{code}
{-"\underline{\textsc{Agda}_{\phantom{g}}
              \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad}"-}

data Ty : Set where  I : Ty
                     B : Ty 

data Val : Ty -> Set where
  IV  : ℕ    -> Val I
  BV  : Bool -> Val B

plusV : Val I -> Val I -> Val I
plusV (IV n) (IV m) = IV (n + m)

ifV : Val B -> {t : Ty} -> Val t -> Val t -> Val t
ifV (BV b) v1 v2 = if b then v1 else v2

{-""-}

data Expr : Ty -> Set where
  VAL   : {t : Ty} -> Val t -> Expr t
  PLUS  : Expr I -> Expr I -> Expr I
  IF    : Expr B ->
          {t : Ty} -> Expr t -> Expr t -> Expr t
{-""-}
eval : {t : Ty} -> Expr t -> Val t
eval (VAL v)        = v
eval (PLUS e1 e2)   =
  plusV  (eval e1) (eval e2)
eval (IF e0 e1 e2)  =
  ifV (eval e0) (eval e1) (eval e2)
\end{code}
