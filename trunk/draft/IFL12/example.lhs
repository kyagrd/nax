%include lhs2TeX.fmt
%include includelhs2tex.lhs

\begin{table}[h]
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
Instead, to define recursive types one uses a fixpoint type operator
|Mu[kappa] : (kappa -> kappa) -> kappa| over non-recursive base structures of kind
|kappa -> kappa| (\eg, |(L a) : * -> *|).
Nax provides the usual data constructor |In[kappa]| to construct
recursive values of the type |Mu[kappa]|.
|In[kappa]| is used to defining the normal constructor functions of recursive types
(\eg, |nil| and |cons|).

\quad
However, one cannot freely eliminate (or destruct) values of $\mu$ types.
In Nax one cannot patten match against |In[kappa] e|. Instead Nax 
provides several well-behaved (\ie, always
terminating) Mendler-style recursion combinators, such as {\bf mcata},
that work naturally over $\mu$ types, even with indices. 

\quad 
To support type inference, Nax requires programmers to annotate Mendler-style
combinators with index tranformers. For instance, Nax can infer that the term
|(\ x -> mcata { {i} {j} . T2 {j} {i} } x with {-"\,\cdots"-})| has type |T1 {i} {j} -> T2 {j} {i}|
using the information in the index transformer
{\tiny |{ {i} {j} . T2 {j} {i} }|}.
\end{tcolorbox}
\caption{\textsc{Nax} features:
	|deriving fixpoint|, |synonym|, $\mu$, {\tt In}, and {\bf mcata}}
\vskip-4ex
\label{tbl:naxfeatures}
\end{table}

\section{The trilingual Rosetta Stone}
\label{sec:example}

In this section, we introduce three examples (Figs.\;\ref{fig:eval},
\ref{fig:glist} and \ref{fig:compile}) that use term indexed datatypes
to enforce program invariants. Each example is written in three
different languages -- like the Rosetta Stone
-- Haskell on the left, Nax in the center,  and Agda on the right.
We have crafted these programs to look as similar as
possible, by choosing the same identifiers and syntax structure whenever
possible, so that anyone already familiar with Haskell-like languages
or Agda-like languges will understand our Nax programs
just by comparing them with the programs on the left and right.
The features unique to Nax are summarized in Tabel\;\ref{tbl:naxfeatures}.

The three examples we introduce are the following:
\begin{itemize}\vspace*{-.5ex}
\item A type preserving evaluator for a simple expression language
(Sect. \ref{ssec:eval}),
\item A generic |Path| datatype that can be specialized to various
list-like structures with indices (Sect. \ref{ssec:glist}), and
\item A stack safe compiler for the same simple expression lagnauge,
which uses the |Path| datatype (Sect. \ref{ssec:compile}).
\end{itemize}
We adopted the examples from Conor McBride's keynote talk \cite{McBride12}
at ICFP 2012 (originally written in Agda). All the example code was tested
in GHC 7.4.1 (should also work in later versions such as GHC 7.6.x),
our prototype Nax implementation, and Agda 2.3.0.1.

%include example_eval.lhs

%include example_glist.lhs

%include example_compile.lhs

