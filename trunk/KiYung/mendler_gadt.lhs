%include includelhs2tex.lhs
\subsection{Indexed datatypes (GADTs)} \label{ssec:tourIndexed}
%format NV = N"_{\!"V"}"
%format CV = C"_{\!"V"}"
%format nilv = nil"_{\!"V"}"
%format consv = cons"_{\!"V"}"

\index{GADT}
\index{generalized algebraic datatype}
\index{datatype!generalized algebraic}
\index{datatype!GADT}
\index{datatype!indexed}
A recent, popular extension to the GHC Haskell compiler is generalized
algebraic datatypes (GADTs) \cite{She05}. In our nested examples, the
variation of type indices always occurred in the arguments of the data
constructors. GADTs are indexed datatypes, where the index may vary in
the result types of the data constructors. Haskell's normal |data| 
declaration, which uses an ``equation'' syntax, 
makes the assumption that the result types of every constructor
is the ``same'' type with no variation. GHC's GADT datatype extension
 is more expressive than the recursive |data| declaration.
The GHC compiler extends the |datatype| syntax, so that
each datatype constructor is given its full type.
The datatype definition for vectors (or size indexed lists) is a prime example:
\index{vector}

\begin{code}
data Vec p i where
  NV :: Vec p Z
  CV :: p -> Vec p i -> Vec p (S i)
\end{code}.
Note, the indices\footnote{The |Z| and |S| used in |Vec| are type level
representations of natural numbers, which are empty types that are not
inhabited by any value. They are only intend to be used as indices.
%% We make this clear so that the reader may not confuse them with
%% the data constructors |Z| and |S| of |Nat| at the value level,
%% which we used in the previous examples.
} vary in the \emph{result types} of
the data constructors: |Z| in the type of |NV| and |(S i)| in the type of |CV|.

Nested datatypes, which we discussed earlier, are a special case of
indexed datatypes that happened to be expressible within
the recursive type equation syntax of Haskell, because the indices only vary
in the recursive arguments of the data constructors, but not in the result type.
\index{bush}
For a clearer comparison, we express the bush datatype in GADT syntax as
follows: \footnote {We can translate any recursive type equation into
a definition using the GADT syntax since GADTs are indeed \emph{generalized}
algebraic datatypes.}

\begin{code}
data Bush i where
  NB :: Bush i
  CB :: i -> Bush (Bush i) -> Bush i
\end{code}
Note, the type argument varies in second argument of |CB|, which is
|Bush (Bush i)|, but both the result type of |NP| and |CP| are |Bush i|.

In Figure \ref{fig:vec}, 
we define the vector datatype |Vec| as |Mu1 (V p) i|, in the Mendler style.
That is, we apply |Mu1| to the partial application of the base |V| to
the parameter |p|, and then apply the resulting fixpoint to the index |i|.
The base datatype |V p r i| is a GADT with a parameter |p| and an index |i|.
Recall that by convention we place the parameter |p| before
the type argument |r| for recursion points, followed by the index |i|.
\index{parameter}
\index{index}
\index{type!parameter}
\index{type!index}
We can express the |copy| function that traverses a given vector and
reconstructs that vector with the same elements, in the Mendler style,
using Mendler-style iteration combinator |mcata1| at kind $* -> *$.
We can express the |switch2| function that switches every two elements of
the given vector, in the Mendler style, using the course-of-values iteration
combinator |mhist1| at kind $* -> *$.
\index{Mendler-style!course-of-values iteration}
The definitions for |mcata1| and |mhist1| are exactly the same as
the definitions for |mcata0| and |mhist0|, except that |mcata1| and |mhist1|
have richer type signatures
(see Figures \ref{fig:rcombty} and \ref{fig:rcombdef}).
Thus, defining functions using |mcata1| and |mhist1| is no more complicated
than defining the functions for regular datatypes using |mcata0| and |mhist0|.
The one proviso to this statement is that we need to give explicit
type signatures for |phi| because GHC does not support type inference
for higher-rank types (\ie, types with inner $\forall$s that are not top-level).
Again, in a language where the Mendler-style combinators were
language constructs rather than functions, we believe this annoying burden
could be lifted.

\begin{figure*}\small
$\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!$
\begin{minipage}{.7\textwidth}
%include mendler/VecG.lhs
\end{minipage}
\begin{minipage}{.4\textwidth}
%include mendler/Vec.lhs
\end{minipage}
\caption{Recursion (|copy|) and course-of-values recursion (|switch2|)
over size indexed lists (|Vec|) expressed in terms of |mcata1| and |mhist1|.}
\label{fig:vec}
\end{figure*}

