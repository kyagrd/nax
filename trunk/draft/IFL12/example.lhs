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

The three examples we introduce are the following:
\begin{itemize}
\item A type preserving evaluator for a simple expression language
(Sect. \ref{ssec:eval}),
\item A generic |Path| datatype that can be specialized to various
list-like structures with indices (Sect. \ref{ssec:glist}), and
\item A stack safe compiler for the same simple expression lagnauge,
which uses the |Path| datatype (Sect. \ref{ssec:compile}).
\end{itemize}
We adopted the examples from Conor McBride's keynote talk \cite{McBride012} at ICFP 2012
(originally written in Agda). All the example code was tested in GHC 7.4.1 (should also work
in later versions such as GHC 7.6.x), our prototype Nax implementation,
and Agda 2.3.0.1.


%include example_eval.lhs

%include example_glist.lhs

%include example_compile.lhs

