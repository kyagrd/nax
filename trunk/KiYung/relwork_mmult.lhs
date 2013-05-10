%include includelhs2tex.lhs

\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes #-}

import Prelude hiding (take, succ)

data Mu0 f = In0 { unIn0 :: f(Mu0 f) } -- use of |UnIn0| is restricted

data N r = Zero | Succ r
type Nat = Mu0 N
zero    = In0 Zero
succ n  = In0 (Succ n)

data L a r = Nil | Cons a r
type List a = Mu0 (L a)
nil        = In0 Nil
cons x xs  = In0 (Cons x xs)
\end{code}
\end{comment}

\section{More Mendler-style recursion schemes} \label{sec:relwork:mult}
There are more Mendler-style recursion schemes other than the recursion schemes
discussed in Chapter~\ref{ch:mendler}. We introduce two of them here.

\paragraph{Simultaneous iteration.}
\citet{UusVen00} studied course-of-value iteration (\aka\ histomorphism)
and \emph{simultaneous iteration} (\aka\ multimorhpism). They formulate
these two recursion schemes in both conventional and Mendler style, and
show both formulations are equivalent provided that the base structures
for recursive types are functors (\ie, positive). We have already discussed
Mendler-style course-of-values iteration in previous chapters.
Here, we introduce Mendler-style simultaneous iteration over
multiple recursive values, using the examples adopted from \citet{UusVen00}.
For simplicity, we only consider simultaneous iteration
over two recursive values, which can be transcribed into Haskell as follows:
%format mmult = "\textbf{mmult}"
%format mmult0 = mmult"_{*}"
%format r1
%format r2
%format f1
%format f2
%format x1
%format x2
\begin{singlespace}
\begin{code}
mmult0 :: (forall r1 r2. (r1 -> r2 -> a) -> f1 r1 -> f2 r2 -> a) -> Mu0 f1 -> Mu0 f2 -> a
mmult0 phi (In0 x1) (In0 x2) = phi (mmult0 phi) x1 x2
\end{code}
\end{singlespace}\vspace*{2mm}
\noindent
This recursion scheme simplifies function definitions
that simultaneously iterate over two recursive arguments.
For example, we can define |lessthan :: Nat -> Nat -> Nat|
and |take :: Nat -> List a -> List a| as follows:
\begin{singlespace}
\begin{code}
lessthan :: Nat -> Nat -> Bool
lessthan = mmult0 phi where  phi lt Zero      Zero      = False
                             phi lt Zero      (Succ _)  = True
                             phi lt (Succ _)  Zero      = False
                             phi lt (Succ m)  (Succ n)  = lt m n
{-""-}
take :: Nat -> List a -> List a
take = mmult0 phi where  phi lt Zero      _            = nil
                         phi lt (Succ _)  Nil          = nil
                         phi lt (Succ n)  (Cons x xs)  = cons x (take n es)
\end{code}
\end{singlespace}\noindent
Note that the |phi| functions above are very similar to how one would typically
define |lessthan| and |take| using general recursion in Haskell. Although
it is possible to define these functions by multiple nested uses of |mit0|,
it would not end up as simple as above (try it yourself!).

The termination behavior of simultaneous iteration (|mmult|)
has not been studied well when negative datatypes are involved.
We do not know of any studies that tried to embed |mmult| into
a strongly normalizing typed lambda calculus either.
For course-of-values iteration (\McvIt) or recursion (\McvPr),
on the other hand, we found a conterexample that \McvIt\ does not terminate
for negative datatypes (Figure~\ref{fig:LoopHisto} in \S\ref{ssec:tourHist0},
p\pageref{fig:LoopHisto}), and we also showed that \McvPr\ can be embedded
into \Fixi\ (or \Fixw) assuming monotonicity (\S\ref{sec:fixi:cv}).

\paragraph{Primitive recursion with uncasting operation.}
A recursion scheme size of index

TODO

See \S\ref{sec:futwork:mprsi} for our motivating example
and further discussions.

