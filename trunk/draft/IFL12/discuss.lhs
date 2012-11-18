%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{Discussions} \label{sec:discuss}
Indexed types (\eg, |Val| in Fig.\;\ref{fig:eval}) are
classified by kinds (\eg, |Ty -> *|). What do valid kinds look like?
Sorting rules define kind validity (or, well-sortedness).
Different programming languages, that support term indices, have
made different design choices.
In this section, we compare the sorting rules of Nax with the sorting rules
of other languages (Sect.\;\ref{ssec:sorting}). Then, we
compare the class of indexed datatypes supported by Nax with
those supported in other languages (Sect.\;\ref{ssec:sortingEx}).

\subsection{Universes, Kinds, and Well-sortedness} \label{ssec:sorting}

The concrete syntax for kinds appears similar among Haskell, Nax, and Agda.
For instance, in Fig.\;\ref{fig:eval}, the kind |Ty -> *| has exactly the same
textual representation in all three of the languages. However, each language
has its own universe structure, kind syntax, and sorting rules,
as summarized in Fig.\;\ref{fig:sorting}. 

Figure \ref{fig:sortingEx}
illustrates differences and similarities between the mechanism
for checking well-sortedness, by comparing the justification for
the well-sortedness of the kind |List Ty -> *|.
The important lessons of Figure \ref{fig:sortingEx} are
that the Nax approach is closely related to \emph{universe subtyping} in Agda,
and, the datatype promotion in Haskell is closely related to
\emph{universe polymorphism} in Agda. 

\afterpage{
\begin{figure}[t]
\hspace*{-3ex} \centering
\begin{tabular}{ccc}
\textsc{Haskell} \textcolor{gray}{\texttt{+ DataKinds}} &
\textsc{Nax} &
\textsc{Agda} 
\\
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
\begin{minipage}{.35\linewidth}\small\centering
term/type/kind/sort merged into one pseudo-term syntax
\end{minipage}
\\~\\
\begin{minipage}{.36\linewidth}
\inference[($->$)]{\Jki |kappa1 : BOX| & \Jki |kappa2 : BOX|}{
     \Jki |kappa1 -> kappa2 : BOX|}
~\vskip.5ex
\inference[($\uparrow_{|*|}^{|BOX|}$)]{
          \Jty T : |*|^n -> |*| \qquad~~\quad \\
          \Jki |kappa : BOX|~\text{for each}~\kappa\in\overline{\kappa}}{
     \Jki T\,\overline{\kappa} : |BOX|}
~\vskip.5ex
\end{minipage}
&
\begin{minipage}{.33\linewidth}
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
\inference[($->$)]{||- \kappa_1 : \star_i & ||- \kappa_2 : \star_i}{
                   ||- \kappa_1 -> \kappa_2 : \star_i}
~\vskip1ex
\inference[(|<=|)]{||- \kappa : s & s \leq s'}{||- \kappa : s'}
~\\
\end{minipage}
\end{tabular}
\caption{Universes, kind syntax, and selected sorting rules
   of Haskell, Nax, and Agda.
   Haskell's and Nax's kind syntax are simplified to exclude kind polymorphism.
   Agda's (|->|) rule is simplified to only allow non-dependent kind arrows.}
\label{fig:sorting}
\end{figure}

\begin{figure}[h!]
\vskip-3ex
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
\caption{Justifications for well-sortedness of the kind |List Ty -> *|
         in Nax, Haskell, Agda}
\label{fig:sortingEx}
\end{figure}
} %%%%%%%%%%%%%%%%%%%%% end afterpage


In Nax, we may form a kind arrow |{A} -> kappa|
whenever |A| is a type (\ie, $\Jty |A : *|$). Note that types may only appear
in the domain (the left-hand-side of the arrow) but not in the codomain 
(the right-hand-side of the arrow).  Modulo right associativity of arrows
(\ie, |kappa1 -> kappa2 -> kappa3| means |kappa1 -> (kappa2 -> kappa3)|),
kinds in Nax always terminate in |*|. For example,\footnote{
	Nax implementation allows programmers to omit curly braces in kinds
	when it is obvious that the domain of arrow kind is a type,
	rather than a kind. For instance, Nax understnads |Nat -> *| as
	|{Nat} -> *| since |Nat| is obviously a (nullary) type constructor
	because it starts with an uppercase letter.
	In Sect.\ref{sec:example}, we omitted curly braces to help readers 
	compare Nax with other languages (the Rosetta stone approach).
	From now on, we will consistently put curly braces for clarity.} \\ $~$
\quad |* -> * -> *|, \qquad |{Nat} -> {Nat} -> *|, \qquad
|({Nat} -> *) -> {Nat} -> *|. \\
The sorting rule (\raisebox{1pt}{\tiny\{\}}$->$) could be understood as
a specific use of universe subtyping (|* <= BOX|) hard-wired within
the arrow formation rule. Agda needs a more general notion of
universe subtyping, since Agda is a dependently typed language
with stratified universes, which we will shortly explain.

Agda has countably many stratified type universes for several good reasons.
When we from a kind arrow |kappa1 -> kappa2| in Agda, the domain |kappa1| and 
the codomain |kappa2| must be the same universe (or, sort), as specified by
the (|->|) rule in Fig.\;\ref{fig:sorting}, and the arrow kind also lies in
the same universe. However, requiring |kappa1|, |kappa2|, and |kappa1 -> kappa2|
to be in exactly the same universe can cause a lot of code duplication.
For example, $|List Ty| -> \star_0$ cannot be justified by the (|->|) rule
since $||- |List Ty| : \star_0$ while $||- \star_0:\star_1$. To work around
the universe difference, one could define datatypes |List'| and |Ty'|,
which are isomorphic to |List| and |Ty|, only at one higher level, such that
$||- |List' Ty'| : \star_1$. Only then, one can construct
$|List' Ty'| -> \star_0$. Furthermore, if one needs to form
$|List Ty| -> \star_1$ we would need yet another set of
duplicate datatypes |List''| and |Ty''| at yet another higher level.
Universe subtyping provides a remedy to such a code duplication problem
by allowing objects in a lower universe to be considered as objects
in a higher universe. This gives us a notion of subtyping such that
$\star_i \leq \star_j$ where $i \leq j$.\footnote{
	See Ulf Norell's thesis \cite{Norell07thesis} (Sect.\;1.4)
	for the full description on universe subtyping.}
With universe subtyping, we can form arrows from |Ty| to any level of universe
(\eg, $|List Ty| -> \star_0$, $|List Ty| -> \star_1$, $\dots$). 
Relating Agda's universes to sorts in Haskell and Nax, $\star_0$ and $\star_1$
correspond to |*| and |BOX|. So, we write |*| and |BOX| instead of $\star_0$
and $\star_1$ in the justification of well-formedness of |List Ty -> *|
in Agda, to make the comparisons align in Fig.\;\ref{fig:sortingEx}.

In addition to universe subtyping, Agda also supports
universe polymorphism,\footnote{See 
\url{http://wiki.portal.chalmers.se/agda/agda.php?n=Main.UniversePolymorphism}.}
which is closely reated to datatype promotion. In fact, it is more intuitive to
understand the datatype promotion in Haskell as a special case of
universe polymorphism. Since there are only two universes |*| and |BOX|
in Haskell, we can think of datatypes like |List| and |Ty| are defined
polymophically at both |*| and |BOX|. That is, |List : BOX -> BOX| as well as
|List : * -> *|, and similarly, |Ty : BOX| as well as |Ty : *|.
So, |List : BOX -> BOX| can be appplied to |Ty : BOX| at kind level,
just as |List : * -> *| can be applied at type level.

In summary, Nax provides a new way of forming kind arrows by allowing
types, which are already fully applied at the type level, as the domain
of an arrow.
On the contrary, Haskell first promotes type constructors (\eg, |List|)
and their argument types (\eg, |Ty|) to the kind level, and everything else
(application of |List| to |Ty| and kind arrow formation) happens at
kind level.

\subsection{Nested Term Indices and Datatypes Containing Types}
\label{ssec:sortingEx}

\begin{figure}
\qquad\begin{minipage}{.8\linewidth}
%include Env.lnax
~\\
%include Env.lagda
\end{minipage}
\caption{Environments of stateful resources
	indexed by the length indexed list of states}
\label{fig:env}
\end{figure}

\begin{figure}
\qquad\begin{minipage}{.5\linewidth}
$\underline{
 \textsc{Haskell}~
 \textcolor{gray}{
  \texttt{+}\;\texttt{GADTs},\;\texttt{DataKinds},\;\texttt{PolyKinds}}
 \phantom{_{g_g}} \qquad\qquad\qquad
 }$ \\ \vskip-1ex
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
\end{figure}

Nax supports nested term indices while Haskell's datatype promotion cannot.
Examples in Sect.\;\ref{sec:example} only used rather simple
indexed datatypes, whose terms indices are of non-indexed types
(\eg, |Nat|, |List Ty|). One can imagine more complex indexed datatypes,
where some term indices are themselves of term-indexed datatypes.
Such nested term indices are often useful in dependently typed programming.
For instance, \citet{BraHam10} used an environment datatype with nested term
indices in the implemention of their EDSL for verified resource usage protocols.
Figure \ref{fig:env} illustrates transcriptions of their environment datatype
(|Env|), originally written in Idris \cite{Brady11}, into Nax and Agda.
The datatype |Env| is indexed by a length indexed list (|Vec|), which is again
indexed by a natural number (|n|). Note that the nested term-index $n$ appears
inside the curly braces nested twice (|{Vec st {n}}|). There is no Haskell
transcription for |Env| because datatype promotion is limited to datatypes
without term indices.

On the contrary, Haskell supports promoted datatypes that hold types as
elements, although limited to types without term indices, while Nax does not.
The heterogeneous list datatype (|HList|) in Fig.\;\ref{fig:hlist} is
a well-known example\footnote{The |HList| library in Haskell by
\citet{HList-HW04} was originally introduced using type class constraints,
rather than using GADTs and other relatively new extensions.}
that uses datatypes containing types.
Note that |HList| is index by |List{-"\;"-}*|, which is a promoted list
whose elements are of kind |*|, that is, element are types.
For instance, |hlist| in Fig.\;\ref{fig:hlist} contains
three elements |3 : Int|, |True : Bool|, and |(1 :.2 :. Nil) : List Int|,
and its type is |HList (Int :. Bool :. List Int :. Nil)|.

