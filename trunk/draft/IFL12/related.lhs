%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{Related Work} \label{sec:related}

\paragraph{Singleton types{\rm ,}\!} first coined by \citet{Hayashi91},
has been used in lightweight verification by simulating dependent types
\cite{XiPfe98,KisSha07}. \citet{SheHooLin05} demonstrated that singleton types
can be defined just like any other datatypes in Omega \cite{SheardOmega04},
a language equipped with GADTs and rich kinds structure. Our universe and
kind structure are much simpler (\eg, no user defined kinds in Nax) than Omega,
yet singleton types are definable with less worries for code duplication
across different universes. Singleton types are typically indexed by
the values of their non-singleton counterparts. For example,
in Fig\;\ref{fig:env}, singleton natural numbers (|SNat|) are indexed by
natural numbers (|Nat|).  Note that we can index datatypes by singleton types
in Nax, while datatype promotion cannot (recall Sect.\;\ref{ssec:sortingEx}).
For instance |Env'| indexed by |SNat| in Fig.\;\ref{fig:env} is a more
faithful transcription of the dependently typed version than |Env| discussed
earlier in Sect.\;\ref{ssec:sortingEx}, since |Env'| has a direct handle
on size of the environment at type level, just by referring to the |SNat| index,
without extra type level computation or reasoning on the vector index.

\paragraph{The kind arrow |({A}->kappa)|{\rm ,}\!} from a type to a kind,
predates Nax. Our kind syntax in Fig.\;\ref{fig:sorting}, although
developed independently, happens to coincide with the kind syntax of Deputy
\cite{ConHarAndGayNec07}, a dependently typed system for low-level
imperative languages with variable mutation and heap-allocated structure.

\paragraph{Curly braces in Nax are different from
		 the curly braces in Agda or SHE.}~

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

