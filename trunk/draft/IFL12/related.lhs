%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{Related Work} \label{sec:related}

\paragraph{Singleton types{\rm ,}\!} first coined by \citet{Hayashi91},
have been used in lightweight verification to simulate dependent types
\cite{XiPfe98,KisSha07}. \citet{SheHooLin05} demonstrated that singleton types
can be defined just like any other datatypes in Omega \cite{SheardOmega04},
a language equipped with GADTs and rich kinds structure. Nax's universe and
kind structure is much simpler than Omega's (\eg, no user defined kinds in Nax),
yet singleton types are definable with fewer worries about code duplication
across different universes. Singleton types are typically indexed by
the values of their non-singleton counterparts. For example,
in Fig\;\ref{fig:env}, singleton natural numbers (|SNat|) are indexed by
natural numbers (|Nat|).  Note that we can index datatypes by singleton types
in Nax, while datatype promotion cannot (recall Sect.\;\ref{ssec:sortingEx}).
For instance |Env'| indexed by |SNat| in Fig.\;\ref{fig:env} is a more
faithful transcription of the dependently typed version than |Env|,
since |Env'| has a direct handle on size of the environment at type level,
just by referring to the |SNat| index, without extra type level computation
on the |Vec| index.

\citet{EisWei12}, in the setting of Haskell's datatype promotion,
automatically derives a singleton type (\eg, singleton natural numbers) and
its associated functions (\eg, addition over singleton natural numbers) from
their non-singleton counterparts (\eg, natural numbers and their addition).
We think it would be possible to apply similar strategies to Nax, and even
better, singleton types for already indexed datatypes would be derivable.

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

In Nax, kind polymorphism is limited to rank-1 since it is well-known that
higher-rank kind polymorphism leads to paradoxes
\cite{hurkens95simplification}.
%%%% there are several more things to cite according to below,
%%%% but I can't figure them out except above
%%%% http://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=4&cad=rja&ved=0CEUQFjAD&url=http%3A%2F%2Fwww.cse.chalmers.se%2Fresearch%2Fgroup%2Flogic%2FTypesSS05%2FExtra%2Fmiquel_sl3.pdf&ei=SkOoULS-Gen-iwKnnYD4DA&usg=AFQjCNEGQtWmZpveVqykzrgpNUBuad7Yjw&sig2=piFq-fSCuWIeL0glaIQ8JA
In fact, type polymorphism in Nax is limited to rank-1 as well since
the type inference is based on Hindley-Milner \cite{Miln78a}.


\paragraph{Concoqtion}\hspace*{-.6ex}\cite{FogPasSeiTah07} is an extention of
MetaOCaml with indexed types. Concoqtion share some similar design principles --
Hindley--Milner-style type inference and \emph{gradual typing by erasure} over
(term) indices. Both in Nax and Concoqtion, a program using indexed types must
still type check within the non-indexed sub-language (OCaml for Concoqtion)
when all indices are erased from the program. However, indices in Concoqtion
differ from term indices discussed in this paper (Nax, datatype promotion, and
dependently typed languages like Agda). Concoqtion indices are Coq terms rather
than OCaml terms. Although this obviously leads to code duplication
between the index world (Coq) and the program world (OCaml), Concoqtion enjoys
practical benefits of having access to the Coq libraries for reasoning about
indices. Comparison of Concoqtion and other related systems can be found in
the technical report by \citet{PasSieTah06}.

