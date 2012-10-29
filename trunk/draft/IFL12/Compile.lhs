%include lhs2TeX.fmt
%include includelhs2tex.lhs


\begin{code}
{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{GADTs},\;\texttt{DataKind},\;\texttt{PolyKind}} }"-}
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
compile (IF e e1 e2) =
  append  (compile e)
          (PCons  (IFPOP  (compile e1)
                          (compile e2))
                  PNil)
\end{code}
