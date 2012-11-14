%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{Additional Related Work} \label{sec:related}
We also discuss the use of singleton types (Sect.\;\ref{ssec:singleton})
and kind polymorphism (Sect.\;\ref{ssec:kindpoly}) in Nax.

\subsection{Singleton Types} \label{ssec:singleton}
Singleton types in Nax TODO

Since \citet{Hayashi91} first coined ``singleton types'', singleton types
were used for lightweight verification by simulating dependent types
\cite{XiPfe98,KisSha07}, and, also used as an implementation idiom for
integrating dependent types into non-dependently typed languages
\cite{XiPfe99,ConHarAndGayNec07}.

\cite{SheHooLin05} observed that express singleton types

Fig.\;\ref{fig:env} 
\cite{SheHooLin05}

\cite{EisWei12}
automatically derive singlton types and functions

\subsection{Kind Syntax (|A -> kappa|)}
We are not the first to come up with arrow kinds whose domains are types.
Our kind syntax in Fig.\;\ref{fig:sorting}, although developed independently,
coincides with the kind grammer of Deputy \cite{ConHarAndGayNec07},
a dependently typed system for annotating low-level imperative programs
(\eg, real-world C programs).

\subsection{Kind Polymorphism} \label{ssec:kindpoly}
In Nax, term-index variables (|i : A|) and type variables (|alpha : *|) may
appear in kinds as well as kind variables (|calX : BOX|).
Polymorphic kind in Nax could either be quantified over kind variables
(|forall calX.kappa|), type variables (|forall alpha.kappa|),
term-index variables (|forall i.kappa|), or combinations of them
(|forall calX alpha i.kappa|). In contrast, datatype promotion only needs to
introduce kind variables (|calX : BOX|)
and polymoprhic kinds (|forall calX.kappa|),

avoid paradoxes

first class polymorphic types

but not first class polymorphic kinds

