%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{Related Work} \label{sec:related}

\paragraph{Singleton types,} first coined by \citet{Hayashi91}, has been used in
lightweight verification by simulating dependent types \cite{XiPfe98,KisSha07}
and also used as an implementation idiom for integrating dependent types into
existing languages \cite{XiPfe99,ConHarAndGayNec07}.

Singleton types in Nax TODO
\cite{SheHooLin05} observed that express singleton types

Fig.\;\ref{fig:env} 
\cite{SheHooLin05}

\cite{EisWei12}
automatically derive singlton types and functions

\paragraph{The kind arrow |({A}->kappa)|,} from a type to a kind, predates Nax.
Our kind syntax in Fig.\;\ref{fig:sorting}, although developed independently,
coincides (except the use of curly braces) with the kind syntax of Deputy
\cite{ConHarAndGayNec07}, a dependently typed system for annotating low-level
imperative programs (\eg, real-world C programs).

\paragraph{Curly braces in Nax are different from the curly braces in Agda or SHE.}~

In Nax, curly braces mean that things inside them are \emph{erasable} (\ie,
must still type correct without all the curly braces). Agda's curly braces
mean that things in them would often be \emph{inferable} so that programmers
may omit them.

The concrete syntax for kinds in SHE\footnote{
	\url{http://personal.cis.strath.ac.uk/conor.mcbride/pub/she/}} appears
almost identical to Nax's concrete kind syntax, even using curly braces around
types. However, SHE's (abstract) kind syntax is virtually identical to the
(abstract) kind syntax of datatype promotion, thus quite different from Nax,
since |{A} :: BOX| in SHE.

\paragraph{Kind polymorphism} in Nax may be polymorphic over term-index
variables (|i : A|) and type variables (|alpha : *|), as well as over
kind variables (|calX : BOX|). That is, polymorphic kinds (or kind schemes)
in Nax may be kind polymorphic (|forall calX.kappa|), type polymorphic
(|forall alpha.kappa|), term-index polymorphic (|forall i.kappa|), or
combinations of them (|forall calX alpha i.kappa|). For example, the kinds of
|P| and |Path| in Fig.\;\ref{fig:glist} are polymorphic over the type variable
|iota: *|.  In contrast, datatype promotion in Haskell only needs to consider
polymorphic kinds (|forall calX.kappa|) quantified over kind variables
(|calX : BOX|) since everything is already promoted to the kind level.

avoid paradoxes TODO cite things realted System $U^{-}$

first class polymorphic types

but not first class polymorphic kinds

