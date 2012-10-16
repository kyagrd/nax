%include lhs2TeX.fmt
%include includelhs2tex.lhs

%% data GList x i j where
%%   GNil   :: GList x i i
%%   GCons  :: x i j -> GList x j k -> GList x i k
%% 
%% 
%% 
%% append :: GList x i j -> GList x j k -> GList x i k
%% append GNil          ys  = ys
%% append (GCons x xs)  ys  = GCons x (append xs ys)


\begin{code}
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
{-"\hspace*{-2ex}"-} -- Doesn't type check without (|* : *|) ext.
{-"\hspace*{-2ex}"-} -- Error message from GHC 7.4.1:
{-"\hspace*{-2ex}"-} -- ~~  Couldn't match kind `|BOX|' against `|*|'
{-"\hspace*{-2ex}"-} -- ~~  Kind incompatibility
{-"\hspace*{-2ex}"-} -- \qquad when matching types:
{-"\hspace*{-2ex}"-} -- \qquad \qquad  |k0 :: BOX|
{-"\hspace*{-2ex}"-} -- \qquad \qquad  |[Ty] :: *|
{-"\hspace*{-2ex}"-} -- ~~  In the return type of a call of `|GCons|'
{-"\hspace*{-2ex}"-} -- ~~  In the expression: |GCons (PUSH v) GNil|
\end{code}
