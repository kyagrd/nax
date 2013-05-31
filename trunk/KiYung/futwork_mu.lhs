%include includelhs2tex.lhs
\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, ImpredicativeTypes #-}
\end{code}
\end{comment}

\section{Conversion between different fixpoint types}
\label{sec:futwork:mu}
In Chapter~\ref{ch:mendler}, we introduced
several Mendler-style recursion schemes by describing them in Haskell,
following certain stylistic conventions. Most of the recursion schemes,
including |mcata| and |mpr|, share the same standard fixpoint representation
in Haskell, denoted by |Mu|, except those recursion schemes involving
inverse operations, such as |msfcata|. The recursion schemes involving
inverse operations operate on the inverse augmented fixpoint, denoted by |Rec|.
Recall the Haskell definitions of the two different fixpoint type operators,
|Mu| and |Rec|, at kind |*|, repeated below:
%format e1
%format e2
\begin{code}
newtype  Mu0 f      = In0 (f (Mu0 f))                      -- |mcata0|, |mprim0|, $\dots$
data     Rec0 f a   = Roll0 (f (Rec0 f a))  | Inverse0 a   -- |msfcata0|
\end{code}
TODO
We want to say that
|Mu0 f| and
|(forall a.Rec0 f a)| are isomorphic

TODO

TODO

TODO

TODO
\begin{figure}
\begin{singlespace}
\begin{code}
data E r = Lam (r -> r) | App r r

type Expr = Mu0 E

type Exp' a = Rec0 E a
type Exp = (forall a. Exp' a)  -- \ie, |(forall a. Rec0 E a)|

exp2expr :: Exp -> Expr  -- \ie, |(forall a. Rec0 E a) -> Mu0 E|
exp2expr = msfcata0 phi where
  phi inv p2r (Lam f)      = In0(Lam((\x -> p2r (f (inv x)))))
  phi inv p2r (App e1 e2)  = In0(App (p2r e1) (p2r e2))
\end{code}
\end{singlespace}
\caption{Conversion from |Rec|-values to |Mu|-values using |msfcata|.}
\label{fig:rec2mu}
\end{figure}
%format msfcata'
\begin{figure}
\begin{singlespace}
\begin{code}
msfcata0  :: (forall r. (a -> r a) -> (r a -> a) -> f (r a) -> a) -> (forall a.   Rec0 f a) -> a
msfcata0 phi r = msfcata' phi r

msfcata'  :: (forall r. (a -> r a) -> (r a -> a) -> f (r a) -> a) ->              Rec0 f a -> a
msfcata' phi (Roll0 x)     = phi Inverse0           (msfcata' phi)  x
msfcata' phi (Inverse0 z)  = z

exp'2expr :: Exp' Expr -> Expr  -- \ie, |Rec0 E (Mu0 E) -> Mu0 E|
exp'2expr = msfcata' phi where
  phi inv p2r (Lam f)      = In0(Lam((\x -> p2r (f (inv x)))))
  phi inv p2r (App e1 e2)  = In0(App (p2r e1) (p2r e2))

expr2exp' :: Expr -> Exp' Expr  -- \ie, |Mu0 E -> Rec0 E (Mu0 E)|
expr2exp' (In0(Lam f))      = Roll0(Lam (\x -> expr2exp' (f (exp'2expr x))))
expr2exp' (In0(App e1 e2))  = Roll0(App (expr2exp' e1) (expr2exp' e2))
\end{code}
\end{singlespace}
\caption{An incomplete attempt to convert from |Mu|-values to |Rec|-values.}
\label{fig:mu2rec}
\end{figure}
%%
\begin{figure}
\begin{spec}
msfcata :: (forall r. (a -> r a) -> (r a -> a) -> f (r a) -> a) -> Rec0 f Id a -> a
msfcata phi x = caseSum x unId (\ f -> f (phi Id))
\end{spec}
\caption{\Fw\ encoding of |msfcata'| in Haskell (see with Figure \ref{fig:proofsf}).}
\label{fig:msfitFw}
\end{figure}

TODO

TODO

TODO

TODO

TODO

TODO

TODO

TODO

TODO

TODO

TODO

TODO


