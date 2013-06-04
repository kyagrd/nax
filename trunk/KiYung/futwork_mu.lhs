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
including |mcata| and |mprim|, share the same standard fixpoint representation
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
We want to establish an isomorphism,\footnote{It is more than an isomorphism
        since we want to preserve the structure as well. But, for simplicity,
        we will just say isomorphism here.}
|Mu0 f| $\simeq$ |(forall a. Rec0 f a)|, between these two fixpoint types,
because we want the Nax language to have one fixpoint rather than two.
Intuitively, there is likely to be a one-to-one mapping between
the |Mu0|-values and the |Rec0|-values, which do not involve the constructor |Inverse0|.
|Mu0| and |Rec0| look structurally isomorphic to each other (if one
does not use |Inverse0|), and we expect that the quantification |forall a| in
|(forall a. Rec0 f a)| would prevent the constructor |Inverse0| from appearing in
values of type |(forall a. Rec0 f a)|.

To establish an isomorphism between |Mu0| and |Rec0|, we must construct two mapping
(or, coercion) functions of type |Mu0 f -> (forall a. Rec0 f a)|
and |(forall a. Rec0 f a) -> Mu0 f| (that are each other's inverse). At first glance, we thought
it would be easier to find a mapping of type |Mu0 f -> (forall a. Rec0 f a)|
by replacing all the |In0|s with |Roll0|s. However, contrary to our
expectation, the other mapping turns out to be more natural.
We illustrate this by using the HOAS datatype as an example.
%% At the end of this section, we will contemplate on why this is so.

Figure \ref{fig:rec2mu} illustrates a mapping from
|(forall a. Rec0 E a)|  to |Mu0 E| implemented using |msfcata0|,
where |E| is a base structure for the untyped HOAS.
Since we have two fixpoint type operators, |Rec0| and |Mu0|,
we can define two recursive datatypes from |E|:
|Exp| defined as |(forall a. Rec0 E a)| and |Expr| defined as |Mu0 E|.
The function |exp2expr :: Exp -> Expr| implements the mapping from
|Rec0|-based HOAS expressions to |Mu0|-based HOAS expressions.
Note, |exp2expr| is defined using |msfcata0|.
This indicates that the mapping from |(forall a. Rec0 f a)| to |Mu0 f|
is admissible within our theory, System \Fi.
%format msfcata'
\begin{figure}[p]
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
%%%%%%%%%%%%%%%%%%%% \end{figure}
\vspace*{1.5em}

%%%%%%%%%%%%%%%%%%%% \begin{figure}
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
%%%%%%%%%%%%%%%%%%%% \end{figure}
\vspace*{1.5em}
%%%%%%%%%%%%%%%%%%%% \begin{figure}
\begin{spec}
msfcata :: (forall r. (a -> r a) -> (r a -> a) -> f (r a) -> a) -> Rec0 f Id a -> a
msfcata phi x = caseSum x unId (\ f -> f (phi Id))
\end{spec}
\caption{\Fw\ encoding of |msfcata'| in Haskell
        (see with Figure \ref{fig:proofsf} on p\pageref{fig:proofsf}).}
\label{fig:msfitFw}
\end{figure}

Figure \ref{fig:mu2rec} illustrates an incomplete attempt to
define a mapping the other way. Finding a mapping from
|(Mu0 E)| to |(forall a. Rec0 E a)| turns out to be difficult (perhaps impossible).
So, we found a mapping (we call |expr2exp'|) from  |(Mu0 E)|, \ie |Expr|,
to |(Rec0 E Expr)|, \ie, |Exp' Expr|, where the formerly universally quantifed |a|
has been instantiated to |Expr|. To define |expr2exp'|, we need
its inverse function |exp'2expr :: Exp' Expr -> Expr|, whose implementation is
structurally identical to |exp2expr| in Figure \ref{fig:rec2mu}, but its type
signature instantiates |a| by |Expr|. Note that |exp'2expr| is defined using
|msfcata'|, whose definition is structurally identical to |msfcata0|, but recurses
over values of |Rec0 f a| rather than |(forall a.Rec0 f a)|. We can prove that
|msfcata'| always terminates by embedding it into System \Fw\ (see
Figure~\ref{fig:msfitFw}). Thus, |exp'2expr| is admissible within our theory.

Lastly, we define |expr2exp'| similar in structure to its inverse |exp'2expr|.
Instead of an abstract recursive call and an abstract inverse, we use
general recursion and the actual inverse function |exp'2expr|.
Here, we use general recursion and pattern matching against |In0| because
we do not know of a Mendler-style recursion scheme to define |expr2exp'|.
We need further investigation on whether |expr2exp'| would always terminate
and whether it is possible to make it work for |Exp| rather than |Exp' Expr|.

%% \paragraph{}
%% Let us contemplate on why the coercion from |(forall a.Rec0 E a)| to |Mu0 E|
%% exists, but the coercion the other way is hard (perhaps impossible) to find.
%% 
%% |msfcata0| can express more functions than |mcata0|
