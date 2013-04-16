\section{Introduction}
During the past decade, the functional programming community achieved
partial success in their goal of maintaining fine-grained properties
by only moderately extending functional language type systems
\cite{CheHin03,CheHin02,Xi03}.
This approach is often called \emph{``lightweight''}\footnote{\eg,
  \url{http://okmij.org/ftp/Computation/lightweight-dependent-typing.html} }
in contrast to the approach taken by fully dependent type systems
(\eg, Coq, Agda).
The Generalized Algebraic Data Type (GADT) extension, implemented
in the Glasgow Haskell Compiler (GHC) and in OCaml\cite{ManStu09,GarNor11}, 
has made the lightweight approach
widely applicable to everyday functional programming tasks.

Unfortunately, most practical lightweight implementations 
lack \textbf{logical consistency} and
\textbf{type inference}. In addition,
they often lack term indexing, so \textbf{term indices are faked}
(or, simulated) by additional type structure replicating the requisite term
structure.
A recent extension in GHC, datatype promotion \cite{YorWeiCrePeyVytMag12},
addresses the issue of term indices, but the issues of
logical consistency and type inference still remain.

Nax is a programming language designed to support both type and
term indexed datatypes,
logical consistency, and type inference.
\begin{description}
\item[$(1)$ Nax is strongly normalizing and logically consistent.]~\\
Types in Nax can be given logical interpretations as propositions
and the programs of those types as proofs of those propositions.
Theories behind strong normalization and logical consistency are
Mendler-style recursion \cite{AhnShe11} discussed in Chapter \ref{ch:mendler}
and the lambda calculi, System \Fi\ and System \Fixi,
discussed in Chapters \ref{ch:fi} and \ref{ch:fixi}.

\item[$(2)$ Nax supports Hindley--Milner-style type inference.]~\\
Nax needs few type annotations. In particular,
annotations for top-level functions, which are usually
required for bidirectional type checking in dependently typed languages,
are unnecessary.
Type annotations are only required when introducing GADTs and as
index transformers attached to pattern matching constructs
(|case| and Mendler-style combinators such as |MIt|) for GADTs.
We will discuss further details on type inference
in Chapter \ref{ch:naxTyInfer}.

\item[$(3)$ Nax programs are expressive and concise.]~\\
Nax programs are similar in size to their Haskell and Agda equivalents
(Sect.\;\ref{sec:example}), yet they still retain logical consistency
and type inference. Despite several features unique to Nax,
explained in Table\;\ref{tbl:naxfeatures}, these features
do not necessarily add verbosity.

\item[$(4)$ Nax supports term indices within a relatively simple type system.]
The type system of Nax (Sect.\;\ref{ssec:sorting}) is based on a
two level universe structure, just like Haskell,
yet it allows nested term indices (Sect.\;\ref{ssec:sortingEx}) as in languages
based on a universe structure of countably many levels (\eg, Coq, Agda).
\end{description}
The detailed mechanism behind (1) and (2) above are discussed in other chapters.
In this Chapter, we demonstrate (3) and (4), through a series of examples
-- a type-preserving evaluator (Sect.\;\ref{ssec:eval}),
a generic path datatype (Sect.\;\ref{ssec:glist}), and
a stack-safe compiler (Sect.\;\ref{ssec:compile}), that programming in Nax 
is as simple as programming in Haskell or Agda.
Then, we discuss the key design principles behind indexed datatypes in Nax
(Sect.\;\ref{ssec:sorting}) and its strengths and limitations
(Sect.\;\ref{ssec:sortingEx}).


\begin{table}
\vskip-4ex
\begin{tcolorbox}[boxsep=-1mm]
\quad The ``|deriving fixpoint T|'' clause following
|data F : {-"\,\overline{k}"-} -> kappa -> kappa where {-"\cdots"-}|
automatically derives a recursive type
synonym |T {-"\,\overline{a}"-} = Mu[kappa](F {-"\,\overline{a}"-}) : kappa|
and its constructor functions.
For instance, the deriving clause below left automatically derives
the definitions below right:\vskip.7ex
\begin{code}
data L : * -> * -> * where  {-"\qquad\qquad"-}  synonym List a = Mu [*] (L a)
  Nil   : L a r                                 nil       = In [*] Nil
  Cons  : a -> r -> L a r                       cons x xs = In [*] (Cons x xs)
    deriving fixpoint List
\end{code}\vskip.5ex
The |synonym| keyword defines a type synonym,
just like Haskell's |type| keyword.

\quad
In Nax, |data| declarations cannot be recursive.
Instead, to define recursive types, one uses a fixpoint type operator
|Mu[kappa] : (kappa -> kappa) -> kappa| over non-recursive base structures
of kind |kappa -> kappa| (\eg, |(L a) : * -> *|).
Nax provides the usual data constructor |In[kappa]| to construct
recursive values of the type |Mu[kappa]|.
|In[kappa]| is used to define the normal constructor functions of
recursive types (\eg, |nil| and |cons|).

\quad
However, one cannot pattern match against |In[kappa] e| in Nax.
Instead, Nax provides several well-behaved (\ie, always
terminating) Mendler-style recursion combinators, such as {\bf mit},
that work naturally over $\mu$ types, even with indices. 

\quad 
To support type inference, Nax requires programmers to annotate Mendler-style
combinators with index transformers. For instance, Nax can infer that the term
|(\ x -> mcata { {i} {j} . T2 {j} {i} } x with {-"\,\cdots"-})| has type |T1 {i} {j} -> T2 {j} {i}|
using the information in the index transformer
{\tiny |{ {i} {j} . T2 {j} {i} }|}.
\end{tcolorbox}
\caption{\textsc{Nax} features:
	|deriving fixpoint|, |synonym|, $\mu$, {\tt In}, and {\bf mcata}}
\vskip-4ex
\label{tbl:naxfeatures}
\end{table}



