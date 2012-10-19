%include lhs2TeX.fmt
%include includelhs2tex.lhs


\begin{code}
{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{GADTs},\;\texttt{DataKind},\;\texttt{PolyKind}} }"-}

data Inst :: [Ty] -> [Ty] -> * where
  PUSH   :: Val t -> Inst ts (t .: ts)
  ADD    :: Inst (I .: I .: ts) (I .: ts)
  IFPOP  :: GList Inst ts ts' ->
            GList Inst ts ts' ->
            Inst (B .: ts) ts'
{-""-}
{-""-}
{-""-}
{-""-}

type Code sc sc' = GList Inst sc sc'

{-""-}
compile :: Expr t -> Code ts (t .: ts)
compile (VAL v) = {-"\textcolor{red}{"-} GCons (PUSH v) GNil {-"}"-}
-- Doesn't type check without (|* : *|).
-- Error message from GHC 7.4.1:
-- ~~  Couldn't match kind `|BOX|' against `|*|'
-- ~~  Kind incompatibility
-- \qquad when matching types:
-- \qquad \qquad  |k0 :: BOX|
-- \qquad \qquad  |[Ty] :: *|
-- ~~  In the return type of a call of `|GCons|'
-- ~~  In the expression: |GCons (PUSH v) GNil|
\end{code}
