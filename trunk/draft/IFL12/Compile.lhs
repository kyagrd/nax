%include lhs2TeX.fmt
%include includelhs2tex.lhs


\begin{code}
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
\end{code}
