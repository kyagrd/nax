%include includelhs2tex.lhs

\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes #-}

import Prelude hiding (head, tail, pred, succ, take)
\end{code}
\end{comment}

\section{Mendler-style co-iteration and co-recursion} \label{sec:relwork:co}
There exist dual constructs to the Mendler-style recursion schemes
discussed in this dissertation. These dual constructs, known as
Mendler-style co-recursion schemes are able to generate possibly
infinite structures. For instance, the Mendler-style co-iteration, \McoIt,
(\aka\ anamorpihsm or fold) is dual to the Mendler-style iteration, \MIt,
(\aka\ catamorpihsm or unfold). Figure~\ref{fig:mcoit0} illustrates
a Haskell transcription \cite{UusVen11} of \McoIt\ in comparison to \MIt,
following the same conventions as in1 Chapter~\ref{ch:mendler}.

\begin{figure}[h]
\begin{singlespace}
\begin{code}
-- Mendler-style co-fixpoint |Nu0| and co-iterator |mcoit0|
data Nu0 f = UnOut0 { out0 :: f(Nu0 f) } -- use of |UnOut0| is restricted
mcoit0  :: (forall r . (a -> r) -> a -> f r) -> a -> Nu0 f
mcoit0 phi v = UnOut0 (phi (mcoit0 phi) v)
{-""-}
-- Mendler-style fixpoint |Mu0| and iterator |mit0|
data Mu0 f = In0 { unIn0 :: f(Mu0 f) } -- use of |UnIn0| is restricted
mit0    :: (forall r . (r -> a) -> f r -> a) -> Mu0 f -> a
mit0 phi x = phi (mit0 phi) (unIn0 x)
\end{code}
\end{singlespace}
\caption{A Haskell transcription of the Mendler-style co-iteration (\McoIt)
	 in comparison to the Mendler-style iteration (\MIt) at kind |*|}
\label{fig:mcoit0}
\end{figure}

Let us first review how we define recursive datatypes. In Mendler-style,
recursive datatypes are defined as fixpoints of (non-recursive) base structures.
For example, we can define datatypes for natural numbers and lists as follows:
\begin{singlespace}
\begin{minipage}{.4\linewidth}
\begin{code}
data N r = Zero | Succ r
type Nat = Mu0 N
zero    = In0 Zero
succ n  = In0 (Succ n)
\end{code}
\end{minipage}
\begin{minipage}{.4\linewidth}
\begin{code}
data L a r = Nil | Cons a r
type List a = Mu0 (L a)
nil        = In0 Nil
cons x xs  = In0 (Cons x xs)
\end{code}
\end{minipage}
\end{singlespace}\vspace*{2mm}
\noindent
The constructor functions |zero|, |succ|, |nil|, |cons| are
ordinary definitions, unlike the special construct |mit0|.
Recall that one can freely use |In0| to construct recursive values
while the use of |unIn0| (\ie, pattern matching |In0|) are restricted
only to define |mit0|. In Mendler-style, One can freely \emph{build up}
recursive values but cannot freely tear them down. To \emph{tear down}
recursive values, one must rely on Mendler-style recursion schemes.
For instance, one cannot define head or tail functions for |List|
by simple pattern matching, but should define them via Mendler-style
recursion schemes.

Conversely, one can freely \emph{tear down} co-recursive values
but cannot freely build them up in Mendler style. To \emph{build up}
co-recursive values, one must rely on Mendler-style co-recursion schemes.
Co-recursive datatypes are defined as co-fixpoint |Nu0| of (non-recursive)
base structures. For example, the stream co-recursive datatype is defined
as follows:
\begin{singlespace}
\begin{code}
data StreamF a r = SCons a r
type Stream a = Nu0 (StreamF a)
head  s = case (out0 s) of SCons h _  -> h
tail  s = case (out0 s) of SCons _ t  -> t
\end{code}
\end{singlespace}
Note that we can define destructor functions for streams,
|head :: Stream a -> a| and |tail :: Stream a -> Stream a|, simply by
pattern matching since we can freely use |out0 :: Nu0 f -> f (Nu0 f)|.
However, without the help the Mendler-style recursion schemes,
one cannot define a constructor function such as
|scons :: a -> Stream a -> Stream a| that builds up
a new stream from an element and an existing stream.
One should use Mendler-style recursion schemes to construct co-recursive values.
For example, we can define a function |upfrom :: Nat -> Stream Nat|, which
builds up a stream starting from a given natural number |n| where each element
is  followed by its successor, as follows:
\begin{singlespace}
\begin{code}
upfrom n = mcoit0 phi n where
  phi upfrm n = SCons n (upfrm (succ n))
\end{code}
\end{singlespace}
For example, |upfrom zero| is a stream of all the natural numbers
starting from zero and counting upwards.
Note that the |phi| function above looks very similar to
the general recursive implementation below, relying on laziness of Haskell:
%format upfrom_g = upfrom"_g"
%format Stream_g = Stream"_g"
%format SCons_g = SCons"_g"
\begin{code}
data Stream_g a = SCons_g a Stream_g

upfrom_g n = SCons_g n (upfrom_g (succ n))
\end{code}
\vspace*{2mm}
Although the streams built up by |upfrom| conceptually stand for infinite
list of values, it does not mean that they diverge. For instance, the stream
|(upfrom zero)| can be understood as a generator that is ready to generate
an arbitrary number, which could be very big but still finite, of naturals
starting from zero. For example, we can write a function
|take :: Nat -> Stream a -> List a|, where |take n s| produces
a list consisting of |n| prefixes of the stream |s|, as follows:
\begin{singlespace}
\begin{code}
take n = mit0 phi n where
  phi tk Zero      = \ _ -> nil
  phi tk (Succ n)  = \ s -> cons (head s) (tk n (tail s))
\end{code}
\end{singlespace}
For example, |(take three (upfrom zero))| produces a list with
three elements |(cons (one (cons two (cons three nil))))|
where |one = succ zero|, |two = succ one| and |three = succ two|.

\citet{matthes98phd} embedded Mendler-style (co-)iteration and 
primitive (co-)recursion into System~\F. \citet{AbeMatUus05} embedded
Mendler-style (co-)iteration into System~\Fw.
\citet{AbeMatUus05} embedded Mendler-style (co-)iteration
in the context of System~\Fw.
\citet{AbeMat04} discovered a reduction preserving embedding
of the Mendler-style primitive recursion into \Fixw, and also
mention that embedding primitive co-recursion is similarly possible
(although not given in the paper due to space restrictions).

