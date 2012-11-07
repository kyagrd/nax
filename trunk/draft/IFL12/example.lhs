%include lhs2TeX.fmt
%include includelhs2tex.lhs

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

\begin{table}[h]
\vskip-3ex
\begin{tcolorbox}[boxsep=-1mm]
\quad The ``|deriving fixpoint|'' clause following 
|data F : {-"\,\overline{k}"-} -> kappa -> kappa where {-"\cdots"-}|
derives a recursive type synonym of |Mu[kappa](F {-"\,\overline{a}"-}) : kappa|
and its constructor functions.
For instance, the deriving clause below left derives the definitions
below right:\vskip.7ex
\begin{code}
data L : * -> * -> * where  {-"\qquad\qquad"-}  synonym List a = Mu [*] (L a)
  Nil   : L a r                                 nil       = In [*] Nil
  Cons  : a -> r -> L a r                       cons x xs = In [*] (Cons x xs)
    deriving fixpoint List
\end{code}\vskip1ex
The |synonym| keyword defines a type synonym,
just like Haskell's |type| keyword.

\quad In Nax, |data| declarations do not directly support recursive definitions.
Instead, one defines recursive types using a fixpoint type operator
|Mu[kappa] : (kappa -> kappa) -> kappa|
over base structures of kind |kappa -> kappa| (\eg, |(L a) : * -> *|).
Nax provides the usual data constructor |In[kappa]| for |Mu[kappa]|, which
can be used for defining constructor functions of recursive types (\eg, |nil|
and |cons|).

\quad However, one cannot freely destruct values of recursive types 
in Nax (\ie, cannot patten match against |In[kappa]|) since recursive types
in Nax are Mendler-style. TODO |mcata|
\end{tcolorbox}
\caption{\textsc{Nax} features:
		|deriving fixpoint|, |synonym|, |Mu|, |In|, and |mcata|}
\vskip-10ex
\label{tbl:naxfeatures}
\end{table}


%include example_eval.lhs

%include example_glist.lhs

%include example_compile.lhs

