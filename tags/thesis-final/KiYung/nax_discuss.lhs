\section{Discussion} \label{sec:discuss}
Indexed types (\eg, |Val| in Figure\;\ref{fig:eval}) are
classified by kinds (\eg, |Ty -> *|). What do valid kinds look like?
Sorting rules define kind validity (or well-sortedness).
Different programming languages that support term indices have
made different design choices.
In this section, we compare the sorting rules of Nax with the sorting rules
of other languages (\S\ref{ssec:sorting}). Then, we
compare the class of indexed datatypes supported by Nax with
those supported in other languages (\S\ref{ssec:sortingEx}).

\subsection{Universes, kinds, and well-sortedness} \label{ssec:sorting}
\index{universe}
The concrete syntax for kinds appears similar among Haskell, Nax, and Agda.
For instance, in Figure\;\ref{fig:eval}, the kind |Ty -> *| has exactly the same
textual representation in all of the three languages. However, each language
has its own universe structure, kind syntax, and sorting rules,
as summarized in Figure\;\ref{fig:sorting}. 

\index{well-sortedness}
Figure\;\ref{fig:sortingEx}
illustrates differences and similarities between the mechanism
for checking well-sortedness, by comparing the justification for
the well-sortedness of the kind |List Ty -> *|.
The important lessons of Figure\;\ref{fig:sortingEx} are
that the Nax approach is closely related to \emph{universe subtyping} in Agda
and the datatype promotion in Haskell is closely related to
\emph{universe polymorphism} in Agda.
\index{datatype promotion}
\index{universe!subtyping}
\index{universe!polymorphism}

\begin{figure}[t]\small
\hspace*{-4ex} \centering
\begin{tabular}{ccc}
\textsc{Haskell} \textcolor{gray}{\texttt{+ DataKinds}} &
\textsc{Nax} &
\textsc{Agda} 
\\
|* : BOX| &
|* : BOX| &
$\star_0 : \star_1 : \star_2 : \star_3 : \cdots$ \\ & &
$\stackrel{\parallel}{|*|}~\,\stackrel{\parallel}{|BOX|}~~\quad\qquad\qquad$
\\
|kappa ::= * || kappa -> kappa | $\mid$
  \textcolor{magenta}{$T\,$}$\overline{\kappa}$
& 
|kappa ::= * || kappa -> kappa | $\mid$
   \textcolor{magenta}{|{A}|}\,|-> kappa|
&
\begin{minipage}{.3\linewidth}\small
$\begin{smallmatrix}
\text{term/type/kind/sort merged}\\
\text{into one pseudo-term syntax}
\end{smallmatrix}$
\end{minipage}
\\
\begin{minipage}{.36\linewidth}
\inference[($->$)]{\Jki |kappa1 : BOX| & \Jki |kappa2 : BOX|}{
     \Jki |kappa1 -> kappa2 : BOX|}
~\vskip.3ex
\inference[($\uparrow_{|*|}^{|BOX|}$)]{
          \Jty T : |*|^n -> |*| \qquad~~\quad \\
          \Jki |kappa : BOX|~\text{for each}~\kappa\in\overline{\kappa}}{
     \Jki T\,\overline{\kappa} : |BOX|}
~\vskip1ex
\end{minipage}
&
\begin{minipage}{.33\linewidth}
~\vskip.8ex
\inference[($->$)]{\Jki |kappa1 : BOX| & \Jki |kappa2 : BOX|}{
        \Jki |kappa1 -> kappa2 : BOX|}
~\vskip1ex
\inference[(\raisebox{1pt}{\tiny\{\}}$->$)]{
        \Jty |A : *| & \Jki |kappa : BOX|}{
        \Jki |{A} -> kappa : BOX|}
~\\
\end{minipage}
&
\begin{minipage}{.36\linewidth}
~\vskip.8ex
\inference[($->$)]{||- \kappa_1 : \star_i & ||- \kappa_2 : \star_i}{
                   ||- \kappa_1 -> \kappa_2 : \star_i}
~\vskip1ex
\inference[(|<=|)]{||- \kappa : s & s \leq s'}{||- \kappa : s'}
~\\
\end{minipage}
\end{tabular}
\begin{singlespace}~\vspace*{-2.5em}
\caption{Universes, kind syntax, and selected sorting rules
   of Haskell, Nax, and Agda.
   Haskell's and Nax's kind syntax are simplified to exclude kind polymorphism.
   Agda's (|->|) rule is simplified to only allow non-dependent kind arrows.}
\label{fig:sorting}
\end{singlespace}
\end{figure}

\begin{figure}[h!]
\vskip-3ex
\hspace*{-3em}
\begin{minipage}{.9\linewidth}
\begin{align*}
\textsc{Nax} & \qquad\quad
  \inference[\tiny(\{\}$->$)]{
  \!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!
            \inference{\Jty |List : * -> *| & \Jty |Ty : *|}{
              \Jty |List Ty : *| }
            & \Jki |* : BOX| }{
     \Jki |{List Ty} -> * : BOX| }
\\ \\
\textsc{Agda}
 & \qquad\qquad\quad
  \inference[\tiny(|->|)]{ \!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!
              \inference[\tiny(|<=|)\!\!\!]{ \!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!
                          \inference[\tiny(|->|)\!\!\!]{
                                 ||- |List : * -> *|
                               & ||- |Ty : *|}{
                            ||- |List Ty : *|}
                          & |* <= BOX|}{
              ||- |List Ty : BOX|}
            & ||- |* : BOX| }{
    ||- |List Ty -> * : BOX| }
\\ \\
\textsc{Haskell} & \qquad\qquad\qquad
  \inference[\tiny(|->|)]{
  \!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!
              \inference[\tiny($\uparrow_\star^\square$)\!\!\!]{
                          \Jty |List: * -> *|
                        & \inference[\tiny($\uparrow_\star^\square$)\!\!\!]{
                              \Jty |Ty : *|}{
                          \Jki |Ty : BOX|} }{
              \Jki |List Ty : BOX|}
            & \Jki |* : BOX| }{
    \Jki |List Ty -> * : BOX| }
\\ \\
\raisebox{15pt}{$
\mathop{
\mathop{\qquad~~\textsc{Agda}_{\phantom{g_g}}\!\!\!\!}
\limits_{+ ~ \text{universe}}}
\limits_{\text{polymorphism}}$}
& \qquad\qquad\quad
  \inference[\tiny(|->|)]{
  \!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!
              \inference{
                          \inference{
                              ||- |List| : \forall\{i\} -> \star_i -> \star_i}{
                            ||- |List: BOX -> BOX|}
                        & \inference{
                              ||- |Ty| : \forall\{i\} -> \star_i}{
                            ||- |Ty : BOX|} }{
              ||- |List Ty : BOX|}
            & ||- |* : BOX| }{
    ||- |List Ty -> * : BOX| }
\end{align*}
\end{minipage}~
\caption{Justifications for well-sortedness of the kind |List Ty -> *|
         in Nax, Haskell, Agda.}
\label{fig:sortingEx}
\end{figure}


In Nax, we may form a kind arrow |{A} -> kappa|
whenever |A| is a type (\ie, $\Jty |A : *|$). Note that types may only appear
in the domain (the left-hand side of the arrow) but not in the codomain 
(the right-hand side of the arrow).  Modulo right associativity of arrows
(\ie, |kappa1 -> kappa2 -> kappa3| means |kappa1 -> (kappa2 -> kappa3)|),
kinds in Nax always terminate in |*|. For example,\footnote{
	The Nax implementation allows programmers to omit curly braces in kinds
	when the domain of an arrow kind obviously looks like a type.
	For instance, |Nat -> *| is considered as |{Nat} -> *|
	since |Nat| is obviously a type because it starts with an uppercase.
	In \S\ref{sec:example}, we omitted curly braces to help readers 
	compare Nax with other languages.
	From now on, we will consistently put curly braces in kinds.}
|* -> * -> *|, |{Nat} -> {Nat} -> *|, and |({Nat} -> *) -> {Nat} -> *|
are valid kinds in Nax.
The sorting rule (\raisebox{1pt}{\tiny\{\}}$->$) could be understood as
a specific use of universe subtyping (|* <= BOX|) hard-wired within
the arrow formation rule. Agda needs a more general notion of
universe subtyping, since it is a dependently-typed language
with stratified universes, which we will shortly explain.
\index{universe!subtyping}

Agda has countably many stratified type universes for several good reasons.
When we form a kind arrow |kappa1 -> kappa2| in Agda, the domain |kappa1| and 
the codomain |kappa2| must be the same universe (or sort), as specified by
the (|->|) rule in Figure\;\ref{fig:sorting}, and the arrow kind also lies in
the same universe. However, requiring |kappa1|, |kappa2|, and |kappa1 -> kappa2|
to be in exactly the same universe can cause a lot of code duplication.
For example, $|List Ty| -> \star_0$ cannot be justified by the (|->|) rule
since $||- |List Ty| : \star_0$ while $||- \star_0:\star_1$. To work around
the universe difference, one could define the datatypes |List'| and |Ty'|,
which are isomorphic to |List| and |Ty|, only at one higher level, such that
$||- |List' Ty'| : \star_1$. Only then, can one construct
$|List' Ty'| -> \star_0$. Furthermore, if one needs to form
$|List Ty| -> \star_1$, we would need yet another set of
duplicate datatypes |List''| and |Ty''| at yet another higher level.
Universe subtyping provides a remedy to such a code duplication problem
by allowing objects in a lower universe to be considered as objects
in a higher universe. This gives us a notion of subtyping such that
$\star_i \leq \star_j$ where $i \leq j$.\footnote{
	See Ulf Norell's thesis \cite{Norell07thesis} (\S1.4)
	for the full description on universe subtyping.}
With universe subtyping, we can form arrows from |Ty| to any level of universe
(\eg, $|List Ty| -> \star_0$, $|List Ty| -> \star_1$, $\dots$). 
Relating Agda's universes to sorts in Haskell and Nax, $\star_0$ and $\star_1$
correspond to |*| and |BOX|. So, we write |*| and |BOX| instead of $\star_0$
and $\star_1$ in the justification of well-formedness of |List Ty -> *|
in Agda, to make the comparisons align in Figure\;\ref{fig:sortingEx}.

\index{universe!polymorphism}
In addition to universe subtyping, Agda also supports
universe polymorphism,\footnote{See 
\url{http://wiki.portal.chalmers.se/agda/agda.php?n=Main.UniversePolymorphism}.}
which is closely related to datatype promotion. In fact, it is more intuitive to
understand the datatype promotion in Haskell as a special case of
universe polymorphism. Since there are only two universes |*| and |BOX|
in Haskell, we can think of datatypes such as |List| and |Ty| being defined
polymorphically at both |*| and |BOX|. That is, |List : BOX -> BOX| as well as
|List : * -> *|, and similarly, |Ty : BOX| as well as |Ty : *|.
So, |List : BOX -> BOX| can be applied to |Ty : BOX| at the kind-level,
just as |List : * -> *| can be applied at the type-level.

In summary, Nax provides a new way of forming kind arrows by allowing
types that are already fully applied at the type-level as the domain
of an arrow.
On the contrary, Haskell first promotes type constructors (\eg, |List|)
and their argument types (\eg, |Ty|) to the kind-level, and everything else
(application of |List| to |Ty| and kind arrow formation) happens at
the kind-level.

\subsection{Nested Term Indices and Datatypes Containing Types}
\label{ssec:sortingEx}

\begin{figure}
\begin{singlespace}\vskip-5ex
\small
%include IFL12code/Env.lnax
%include IFL12code/Env.lagda
\end{singlespace}
\vskip-3ex
\begin{singlespace}
\caption{Environments of stateful resources
	indexed by the length-indexed list of states.}
\label{fig:env}
\end{singlespace}
\end{figure}

\begin{figure}
\begin{singlespace}
\qquad\begin{minipage}{.5\linewidth}
$\underline{
 \textsc{Haskell}~
 \textcolor{gray}{
  \texttt{+}\;\texttt{GADTs},\;\texttt{DataKinds},\;\texttt{PolyKinds}}
 \phantom{_{g_g}} \qquad\qquad\qquad
 }$
\begin{code}
data List a = Nil | a :. List a{-"~"-};{-"~"-}infixr :.

data HList :: List {-"\;"-} * -> * where
  HNil  :: HList Nil
  HCons :: t -> HList ts -> HList (t :. ts)

hlist :: HList (Int :. Bool :. List Int :.  Nil)
hlist = HCons 3 (HCons True (HCons (1 :. 2 :. Nil) HNil))
\end{code}
\end{minipage}
\caption{Heterogeneous lists (|HList|) indexed by
	 the list of element types (|List{-"\;"-}*|).}
\label{fig:hlist}
\end{singlespace}
\end{figure}
\index{nested term index}
\index{term index!nested}
Nax supports nested term indices, while Haskell's datatype promotion cannot.
The examples in \S\ref{sec:example} only used rather simple
indexed datatypes, whose term indices are of non-indexed types
(\eg, |Nat|, |List Ty|). One can imagine more complex indexed datatypes,
where some term indices are themselves of term-indexed datatypes.
Such nested term indices are often useful in dependently-typed programming.
For instance, \citet{BraHam10} used an environment datatype with nested term
indices in their EDSL implementation for verified resource usage protocols.
Figure \ref{fig:env} illustrates transcriptions of their environment datatype
(|Env|), originally written in Idris \cite{Brady11}, into Nax and Agda.
The datatype |Env| is indexed by a length indexed list (|Vec|), which is again
indexed by a natural number (|n|). Note that the nested term index $n$ appears
inside the curly braces nested twice (|{Vec st {n}}|). There is no Haskell
transcription for |Env| because datatype promotion is limited to datatypes
without term indices.

On the contrary, Haskell supports promoted datatypes that hold types as
elements, although limited to types without term indices, while Nax does not.
The heterogeneous list datatype (|HList|) in Figure\;\ref{fig:hlist} is
a well-known example\footnote{The |HList| library in Haskell by
\citet{HList-HW04} was originally introduced using type class constraints,
rather than using GADTs and other relatively new extensions.}
that uses datatypes containing types.
Note that |HList| is indexed by |List{-"\;"-}*|, which is a promoted list
whose elements are of kind |*|, that is, the element are types.
For instance, |hlist| in Figure\;\ref{fig:hlist} contains
three elements |3 : Int|, |True : Bool|, and |(1 :.2 :. Nil) : List Int|,
and its type is |HList (Int :. Bool :. List Int :. Nil)|.


\section{Related Work} \label{sec:related}
\index{singlton type}
\paragraph{Singleton types{\rm ,}\!} first coined by \citet{Hayashi91},
have been used in lightweight verification to simulate dependent types
\cite{XiPfe98,KisSha07}. \citet{SheHooLin05} demonstrated that singleton types
can be defined just like any other datatype in Omega \cite{SheardOmega04},
a language equipped with GADTs and a rich kind structure. Nax's universe and
kind structure is much simpler than Omega's (\eg, no user-defined kinds in Nax),
yet singleton types are definable with fewer worries about code duplication
across different universes. Singleton types are typically indexed by
the values of their non-singleton counterparts. For example,
in Figure\;\ref{fig:env}, singleton natural numbers (|SNat|) are indexed by
natural numbers (|Nat|).  Note that we can index datatypes by singleton types
in Nax, while datatype promotion cannot (recall \S\ref{ssec:sortingEx}).
For instance, |Env'| indexed by |SNat| in Figure\;\ref{fig:env} can better
simulate the dependently-typed version than |Env|, since |Env'| has a direct
handle on size of the environment at the type-level, just by referring to
the |SNat| index, without extra type-level computation on the |Vec| index.

\citet{EisWei12}, in the setting of Haskell's datatype promotion,
automatically derived a singleton type (\eg, singleton natural numbers) and
its associated functions (\eg, addition over singleton natural numbers) from
their non-singleton counterparts (\eg, natural numbers and their addition).
We think it would be possible to apply similar strategies to Nax, and even
better, singleton types for already indexed datatypes would be derivable.

\paragraph{The kind arrow |({A}->kappa)|{\rm ,}\!} from a type to a kind,
predates Nax.
\index{kind arrow}
Our kind syntax in Figure\;\ref{fig:sorting}, although developed independently,
happens to coincide with the kind syntax of Deputy \cite{ConHarAndGayNec07},
a dependently-typed system for low-level imperative languages with
variable mutation and a heap allocated structure.

\paragraph{Curly braces in Nax are different from those in Agda or SHE.} ~

In Nax, curly braces mean that the things inside them are \emph{erasable} (\ie,
must still type-correct without all the curly braces). Agda's curly braces
mean that the things in them would often be \emph{inferable} so that programmers
may omit them.

The concrete syntax for kinds in SHE\footnote{
	\url{http://personal.cis.strath.ac.uk/conor.mcbride/pub/she/}} appears
almost identical to Nax's concrete kind syntax, even using curly braces around
types. However, SHE's (abstract) kind syntax is virtually identical to the
(abstract) kind syntax of datatype promotion, thus quite different from Nax,
since |{A} :: BOX| in SHE.

\index{kind polymorphism}
\paragraph{Kind polymorphism}\hspace*{-.7ex} in Nax
may be polymorphic over term-index
variables (|i : A|) and type variables (|alpha : *|), as well as over
kind variables (|calX : BOX|). That is, polymorphic kinds (or kind schemes)
in Nax may be kind polymorphic (|forall calX.kappa|), type polymorphic
(|forall alpha.kappa|), term-index polymorphic (|forall i.kappa|), or
combinations of them (|forall calX alpha i.kappa|). For example, the kinds of
|P| and |Path| in Figure\;\ref{fig:glist} are polymorphic over the type variable
|iota: *|.  In contrast, datatype promotion in Haskell only needs to consider
polymorphic kinds (|forall calX.kappa|) quantified over kind variables
(|calX : BOX|) since everything is already promoted to the kind-level.

In Nax, kind polymorphism is limited to rank-1 since it is well known that
higher-rank kind polymorphism leads to a paradox
\cite{hurkens95simplification}.
%%%% there are several more things to cite according to below,
%%%% but I can't figure them out except above
%%%% http://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=4&cad=rja&ved=0CEUQFjAD&url=http%3A%2F%2Fwww.cse.chalmers.se%2Fresearch%2Fgroup%2Flogic%2FTypesSS05%2FExtra%2Fmiquel_sl3.pdf&ei=SkOoULS-Gen-iwKnnYD4DA&usg=AFQjCNEGQtWmZpveVqykzrgpNUBuad7Yjw&sig2=piFq-fSCuWIeL0glaIQ8JA
In fact, type polymorphism in Nax is limited to rank-1 as well since
type inference is based on Hindley-Milner \cite{Milner78}.


\paragraph{Concoqtion}\hspace*{-.7ex}\cite{FogPasSeiTah07} is an extension of
MetaOCaml with indexed types. Concoqtion shares some similar design principles
--- Hindley--Milner-style type inference and \emph{gradual typing by erasure}
over (term) indices. Both in Nax and in Concoqtion, a program
using indexed types must still type check within the non-indexed sub-language
(OCaml for Concoqtion) when all indices are erased from the program. However,
indices in Concoqtion differ from the term indices discussed in this chapter
(Nax, datatype promotion, and dependently-typed languages like Agda).
Concoqtion indices are Coq terms rather than OCaml terms. Although
this obviously leads to code duplication between the index world (Coq)
and the program world (OCaml), Concoqtion enjoys practical benefits of
having access to the Coq libraries for reasoning about indices.
Comparison of Concoqtion and other related systems can be found in
the technical report by \citet{PasSieTah06}.



\section{Summary and Future Work}
In Nax, programmers can enforce program invariants using indexed types,
without excessive annotations (like functional programming languages)
while enjoying logical consistency (like dependently-typed proof assistants).

There are two approaches that allow term indices without code duplication at
every universe. \emph{Universe subtyping} is independent of the number of
universes. Even scaled down to two universes (|*, BOX|), it adds no additional
restrictions -- term indices can appear at arbitrary depth.
\emph{Universe polymorphism} is sensitive to the number of universes.
Unless there are countably infinite universes, nested term indices are
restricted to depth $n-1$ where $n$ is the number of universes.

On the other hand, universe polymorphism can reuse datatypes at
the term-level (|List a| where |a: *|) at the type-level to contain
type elements (\eg, |List| |*|), which is beyond universe subtyping.
We envision that Nax extended with first-class datatype descriptions
\cite{DagMcb12} would be able express the same concept reflected
at the term level, so that we would have no need for type-level datatypes.

