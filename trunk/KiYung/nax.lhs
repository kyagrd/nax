%include lhs2TeX.fmt
%include greek.fmt
%include forall.fmt
%include agda.fmt
%include IFL12code/includelhs2tex.lhs

\newcommand{\Jtag}[1]{\mathop{\vdash_{\!\!\mathsf{#1}}}}
\newcommand{\Jty}[0]{\Jtag{ty}}
\newcommand{\Jki}[0]{\Jtag{k}}

\chapter{The Nax language}\label{ch:nax} TODO

TODO

\begin{itemize}
\item Based on the idea of the Mendler-style appraoch.
That is, to restrict the elimination of datatypes
rather than to restrict the formation of datatypes.
for consistency, or normalization.
\item distinction between term indices used at type level
and terms used at value level. Full dependent types are more
expressive in the sense that they can build types depending on
runtime values but lacks this distinction.
\item type inference based on small kind annotation, which is
an extension of HM. Full dependently typed languages lack
type inference (they usually do bidirectional type checking,
local type inference)
\end{itemize}

TODO

I am also designing a surface language called Nax that supports
non-recursive datatypes, a recursive type operator $\mu$, and
Mendler-style recursion combinators as language constructs.
Nax supports Hindley-Milner style type inference, with a few type annotations
for indexed types. Nax is designed to be embeddable into System \Fi.
You can find a summary of our progress in defining Nax in Chapter \ref{sec:nax}.

%include nax_examples.lhs

%include nax_discuss.lhs

