%include includelhs2tex.lhs

\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes #-}

import Prelude hiding (head, tail, pred, succ, take)
\end{code}
\end{comment}

\section{Mendler-style co-iteration and co-recursion} \label{sec:relwork:co}
\index{Mendler-style!co-iteration}
\index{Mendler-style!co-recursion}
\index{co-data}
Data structures have natural duals, known as co-data.
Data is characterized by how it is constructed and co-data is
characterized by how it is observed (i.e., destructed).

Mendler-style recursion schemes generalize (or, dualize) naturally to co-data.
We call these generalizations Mendler-style co-recursion schemes.
These co-recursion schemes generate possibly infinite structures. 
For instance, an infinite sequence of natural numbers.

\index{Mendler-style!co-iteration}
\index{anamorphism}
\index{unfold}
The Mendler-style co-iteration, \McoIt, (\aka\ anamorphism or unfold) is
dual to the Mendler-style iteration, \MIt, (\aka\ catamorpihsm or fold).
Figure~\ref{fig:mcoit0} (adapted from \citet{UusVen11}) illustrates
a Haskell transcription of \MIt\ and its dual \McoIt.
%% Readers can compare the two for similarities and differences.
We use the same style of Haskell code used in Chapter~\ref{ch:mendler}.
The reversal of the function arrows is typical of a dual construction.
\index{abstract operation}
Note that domain and the codomain of the abstract operations are flipped:
|(a -> r)|, |(a -> f r)|, |(a -> Nu0 f)| verses
|(r -> a)|, |(f r -> a)|, |(Mu0 f -> a)|.
We illustrate Mendler-style co-iteration at kind |*|.
Mendler-style co-iteration naturally generalizes to higher kinds
just as Mendler-style iteration generalizes to higher kinds.

\begin{figure}
%format unIn0 = unIn"_{*}"
%format UnOut0 = UnOut"_{*}"
\begin{singlespace}
\begin{code}
-- Mendler-style co-fixpoint |Nu0| and co-iterator |mcoit0|
data Nu0 f = UnOut0 { out0 :: f(Nu0 f) } -- use of |UnOut0| is restricted
mcoit0  :: (forall r . (a -> r) -> (a -> f r)) -> (a -> Nu0 f)
mcoit0 phi v = UnOut0 (phi (mcoit0 phi) v)
{-""-}
-- Mendler-style fixpoint |Mu0| and iterator |mit0|
data Mu0 f = In0 { unIn0 :: f(Mu0 f) } -- use of |UnIn0| is restricted
mit0    :: (forall r . (r -> a) -> (f r -> a)) -> (Mu0 f -> a)
mit0 phi x = phi (mit0 phi) (unIn0 x)
\end{code}
\end{singlespace}
\caption{A Haskell transcription of Mendler-style co-iteration (\McoIt)
         in comparison to Mendler-style iteration (\MIt) at kind |*|.}
\label{fig:mcoit0}
\end{figure}

In order to understand co-recursive datatypes, we review recursive datatypes.
In Mendler style, recursive datatypes are defined as fixpoints of
(non-recursive) base structures. For example, we can define datatypes
for natural numbers and lists in two steps:
define the base structure (|N| and |L|) and
take fixpoints of them (using |Mu0|):
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
\end{singlespace}\vspace*{2.2mm}
\noindent
The constructor functions |zero|, |succ|, |nil|, and |cons| are
ordinary definitions defined in terms of |In0|.
Using the conventions described in Chapter~\ref{ch:mendler},
the use of |In0| is unrestricted, but its inverse |unIn0|
(or pattern matching against |In0|) is
restricted. To eliminate a list or a natural number,
one must use a Mendler-style recursion scheme, like |mit0|.
In Mendler style, one can freely \emph{construct}
recursive values but cannot freely destruct them. 
For example, one cannot define head or tail functions for |List|
by simple pattern matching. Instead, one must define them via Mendler-style
recursion schemes.

Conversely, when we define co-data,
one can freely \emph{tear down} their values,
but one cannot freely construct them.
To \emph{construct}
co-recursive values, one must rely on Mendler-style co-recursion schemes.
Co-recursive datatypes are defined as the co-fixpoint |Nu0| of (non-recursive)
base structures. For example, infinite streams are
defined as a co-recursive datatype
as follows:
\index{dataype!co-recursive}
\index{co-recursive datatype}
\begin{singlespace}
\begin{code}
data StreamF a r = SCons a r
type Stream a = Nu0 (StreamF a)

head  s = case (out0 s) of SCons h _  -> h
tail  s = case (out0 s) of SCons _ t  -> t
\end{code}
\end{singlespace}
\index{destructor}
Note that we can define destructor functions for streams,
|head :: Stream a -> a| and |tail :: Stream a -> Stream a|, simply by
pattern matching, since we can freely use |out0 :: Nu0 f -> f (Nu0 f)|.

However, without the help of a Mendler-style co-recursion scheme, one cannot
define a constructor function, such as
|scons{-"\,"-} :: {-"\,"-}a -> Stream a -> Stream a|,
that builds up a new stream from an element and an existing stream. One must
use Mendler-style co-recursion schemes to construct co-recursive values.
This limitation follows from the restriction we place on the use of |UnOut0|.
We can pattern match against a value |(UnOut0 x)| (or freely use
the function |out0|), but we cannot freely use |UnOut0| to construct co-data.
The last step of constructing co-data (applying |UnOut0|) must be done using
a Mendler-style co-recursion scheme, just as the first step of eliminating data
(stripping off |In0|) must be done using a Mendler-style recursion scheme.

As an example of constructing a |Stream|, we define a function
|upfrom :: Nat -> Stream Nat|, which builds up a stream starting from
a given natural number |n| where each element (|n|) is allways followed
by its successor (|succ n|), as follows:
\begin{singlespace}
\begin{code}
upfrom n =  mcoit0 phi n where
              phi upfrm n = SCons n (upfrm (succ n))
\end{code}
\end{singlespace}\noindent
For instance, (|upfrom zero|) is a stream of all the natural numbers,
starting from zero, and counting upwards.

Note that the |phi| function is similar in structure to
the general recursive implementation below, 
which exploits the laziness of Haskell:
%format upfrom_g = upfrom"_g"
%format Stream_g = Stream"_g"
%format SCons_g = SCons"_g"
\begin{code}
data Stream_g a = SCons_g a (Stream_g a)

upfrom_g n = SCons_g n (upfrom_g (succ n))
\end{code}
Although the streams built by |upfrom| conceptually stand for infinite
lists, they do not diverge. The stream
|(upfrom zero)| can be understood as a generator,
ready to generate the next natural number (using |head|)
or the next stream (using |tail|).

For example, we can write a function
|take :: Nat -> Stream a -> List a|, where |take n s| produces
a list consisting of the prefix of length |n| of the stream |s|, as follows:
\begin{singlespace}
\begin{code}
take n = mit0 phi n where
  phi tk Zero      = \ _ -> nil
  phi tk (Succ n)  = \ s -> cons (head s) (tk n (tail s))
\end{code}
\end{singlespace}\noindent
For instance, |(take three (upfrom zero))| produces a list with
three elements starting from zero |(cons (one (cons two (cons three nil))))|
where |one = succ zero|, |two = succ one| and |three = succ two|.

Note that the |phi| function is similar in structure
to how one would typically implement Haskell's standard 
prelude function |take :: Int -> [a] -> [a]| over Haskell lists.
Unlike the Haskell prelude function, which is partial (\eg, |take 2 []|
is undefined), our |take| funciton over streams are total because
|Stream|s are always infinite by definition.

One could define a possibly finite stream by taking the co-fixpoint
over |L|, sharing the same base structure with |List|, as follows:
\begin{singlespace}
\begin{code}
type Stream' a = Nu0 (L a)
head'  s = case out0 s of  Nil       -> Nothing
                           Cons h _  -> Just h
tail'  s = case out0 s of  Nil       -> Nothing
                           Cons _ t  -> Just t
\end{code}
\end{singlespace}\noindent
Here, the destructors |head'| and |tail'| become slightly more complicated
because |Stream'| can be finite, terminating in |Nil|. 

Due to laziness, datatypes in Haskell have characteristics of
both recursive and co-recursive datatypes. However, when we use Haskell
to explain Mendler-style concepts, we always distinguish recursive and
co-recursive datatypes by adhering to the conventions we discussed:
no general recursion except to define the (co-)fixpoint\footnote{
        A word prefixed by `(co-)' refers to the words
        both with and without `(co-)'. That is, (co-)iteration
        refers to both iteration and co-iteration.}
operators themselves (|Mu0|, |Nu0|) and their (co-)recursion schemes
(|mit0|, |mcoit0|). We also restrict the use of |unIn0| and |UnOut0|
as described.

\citet{matthes98phd} extended System~\F\ with Mendler-style (co-)iteration
and primitive (co-)recursion, and studied their properties. 
\citet{AbeMatUus05} embedded
Mendler-style (co-)iteration into System~\Fw.
\index{reduction preserving}
\citet{AbeMat04} discovered a reduction preserving embedding
of Mendler-style primitive recursion into \Fixw. They mention that
an embedding of primitive co-recursion is similarly possible.
%% (although
%% they did not give the embedding in the paper due to space restrictions).

\citet{UusVen11,UusVen99,UusVen99histo} studied Mendler-style recursion
schemes in a categorical setting, while the works mentioned in the paragraph
above are set in the context of typed lambda calculi.
Vene \citet{vene00phd} relates several Mendler-style recursion schemes with
their non Mendler-style counterparts -- (co-)iteration,
primitive (co-)recursion, and course-of-values (co-)iteration.

