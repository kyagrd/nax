%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{TODO discussion} \label{sec:discuss}
To support term indexed types, such as |Val : Ty -> *| in Fig.\;\ref{fig:eval},
the type system needs to allow formation of the kinds for
those term indexed types, such as |Ty -> *|, as valid kinds. In other words,
the class of indexed types supported in a language is determined by
sorting out \emph{``what valid kinds are''} in the language. Thus,
the sorting rules, which define kind validity (or, well-sortedness),
is a core design choice for a programming language that supports term indices.

We discuss the sorting rules of Nax, in comparison with the sorting rules
of other languages (Sect.\;\ref{ssec:sorting}). Then, we introduce examples
that highlights the class of indexed datatypes Nax supports, in comparison
to what other languages supports (Sect.\;\ref{ssec:sortingEx}).
We also discuss the use of singleton types (Sect.\;\ref{ssec:singleton})
and kind polymorphism (Sect.\;\ref{ssec:kindpoly}) in Nax.


\subsection{Universes, kinds, and well-sortedness} \label{ssec:sorting}

The kind annotations on datatypes look very similar among the three languages
in the examples we discussed in Sect.\;\ref{sec:example} (Figs.\;\ref{fig:eval},
\ref{fig:glist}, and \ref{fig:compile}). For instance, the kind |Ty -> *|
has exactly the same textual representation in all the three languages.
Although the textual form of the kinds coincides, each language has its own
universe structure, kind syntax, and sorting (or, kind validity) rules
as summarized in Fig.\;\ref{fig:sorting}.

In a nutshell, the mechanism that allow types at kind level in Nax
is closely related to \emph{universe subtyping} in Agda, and,
the datatype promotion in Haskell is closely related to
\emph{universe polymorphism} in Agda. Figure \ref{fig:sortingEx}
illustrates differences and similarities between the mechanism
for checking well-sortedness, by comparing the justification for
well-sortedness of the kind |List Ty -> *| in each language.

\begin{figure}
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
\\ \\
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

\caption{Universes, kind syntax, and some selected sorting rules
   of Haskell, Nax, Agda.
   Haskell and Nax's kind syntax is simplified, excluding kind polymorphism.
   Agda's (|->|) rule simplified for non-dependent kind arrows.}
\label{fig:sorting}
\end{figure}

\begin{figure}
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

In Nax, we introduce a new way of forming kind arrow |{A} -> kappa|
where |A| is a type (\ie, $\Jty |A : *|$). Note that types can only appear
in the domain (\ie, left-hand-side of the arrow) but not the range
(\ie, right-hand-side of the arrow).  Modulo right associativity of arrows
(\ie, |kappa1 -> kappa2 -> kappa3| means |kappa1 -> (kappa2 -> kappa3)|),
kinds in Nax always end up in |*| (\eg, |* -> * -> *|, |{Nat} -> {Nat} -> *|,
|({Nat} -> *) -> {Nat} -> *|).\footnote{Nax implementation allows programmers
to omit curly braces in kinds when it is obvious that the domain is a type
rather than a kind (\eg, |Nat -> *| really means |{Nat} -> *|).
In Sect.\ref{sec:example}, we omitted curly braces to help readers understand
Nax comparing to other languages with similar syntax  (Rosetta stone approach).
From now on, we will consistently put curly braces everywhere for clarity.}
The sorting rule ($\uparrow_{|*|}^{|BOX|}$) could be understood as a specific
use of universe subtyping (|* <= BOX|) hard-wired with the arrow formation.
Agda needs a more general notion of universe subtyping since Agda is
a dependently typed language with stratified universes, which we will
shortly explain.

Agda has countably many stratified type universes for several good reasons.
When we from a kind arrow |kappa1 -> kappa2| in Agda, the domain |kappa1| and 
the codomain |kappa2| must be the same universe (or, sort), as specified by
the (|->|) rule in Fig.\;\ref{fig:sorting}, and the arrow kind also lies in
the same universe. However, requiring |kappa1|, |kappa2|, and |kappa1 -> kappa2|
to be in exactly the same universe can cause a lot of code duplication.
For example, $|List Ty| -> \star_0$ cannot be justified by the (|->|) rule
since $||- |List Ty| : \star_0$ while $||- \star_0:\star_1$. To work around
the universe difference, one could define datatypes |List'| and |Ty'|,
which is isomorphic to |List| and |Ty| but at one higher level, such that
$||- |List' Ty'| : \star_1$. Only then, one can construct
$|List' Ty'| -> \star_0$. Furthermore, if one needs to form
$|List Ty| -> \star_1$ we would need yet another set of
duplicate datatypes |List''| and |Ty''| at yet another higher level.
Universe subtyping provides a remedy to such a code duplication problem
by allowing objects at lower universe to be considered as objects
at higher universe. This gives us a notion of subtyping such that
$\star_i \leq \star_j$ where $i \leq j$.\footnote{
	This is not the only rule for subtyping in Agda.
 	Another important rule is subtyping between arrows.
	See Ulf Norell's thesis [TODO cite] (Sect.\;1.4) for details.}
With universe subtyping, we can form arrows from |Ty| to any level of universe
(\eg, $|List Ty| -> \star_0$, $|List Ty| -> \star_1$, $\dots$). Relating back to
the datatype promotion in Haskell, $\star_0$ and $\star_1$ corresponds to |*|
and |BOX| in Haskell. So, we wrote |*| and |BOX| instead of $\star_0$ and
$\star_1$ in the Agda sorting rules and in the justification of well-formedness
of |List Ty -> *| in Agda, to make the comparison more apparent.

In addition to universe subtyping, Agda also supports
universe polymorphism,\footnote{
\url{http://wiki.portal.chalmers.se/agda/agda.php?n=Main.UniversePolymorphism}
We only rely on universe subtyping but not universe polymorphism in
our Agda example codes in Figs.\;\ref{fig:eval}, \ref{fig:glist}, and
\ref{fig:compile}.
}
which can be viewed as a generalization of the datatype promotion in Haskell.
In fact, it is more intuitive to understand datatype promotion in Haskell
as a special case of universe polymorphism. Since there are only two
universes |*| and |BOX| in Haskell, we can think of datatypes like |List| and
|Ty| are defined polymophically at both |*| and |BOX|. That is,
|List : BOX -> BOX| as well as |List : * -> *|, and similarly,
|Ty : BOX| as well as |Ty : *|. So, |List : BOX -> BOX| can be appplied to
|Ty : BOX| at kind level, just as |List : * -> *| can be applied at type level.
Haskell kinds must also end up in |*| since Haskell is not a dependently typed
language (\eg, |* -> Nat| may make sense in Agda but nonsense in Haskell),
although it is not evident in the kind syntax. So, there are should be
axillary sorting rules to prevent kinds not to end up with promoted types.

In summary, Nax provides a new way of forming kind arrows by allowing
types, already fully applied at type level, as the domain of an arrow.
On the contrary, Haskell first promotes type constructors (\eg, |List|)
and their argument types (\eg, |Ty|) to kind level, and everything else
(application of |List| to |Ty| and kind arrow formation) happens at
kind level.

\subsection{Deeply indexed datatypes and datatypes containing types}
\label{ssec:sortingEx}

Examples in Sect.\;\ref{sec:example} consisted of rather simple
indexed datatypes, where the terms indices are of datatypes
without any term indices (\eg, |Unit|, |Nat|, |Bool|).
One can imagine more complex indexed datatypes, where some term indices
are themselves of indexed datatypes. Such deeply indexed datatypes are
often useful in dependently typed programming. For instance, \citet{BraHam10}
defines a datatype for environments that contain stateful resources in order
to implement their embedded domain specific language (EDSL) for verified
resource usage protocols. Figure \ref{fig:env} is a transcription of
their environment datatype (|Env|) in Idris into Nax. Note that the datatype
|Env| is indexed by a term of a length indexed list datatype, which is again
indexed by a natural number term. There is no Haskell transcription because
datatype promotion \cite{YorgeyWCJVM12} is limited to datatypes without any
term indices. That is, Nax supports deeply nested datatypes while Haskell's
datatype promotion does not.

\begin{figure}
\qquad\begin{minipage}{.8\linewidth}
%include Env.lagda
% ~\\
%include Env.lnax
\end{minipage}
\caption{Environments of stateful resources
	indexed by the length indexed list of states}
\label{fig:env}
\end{figure}

On the contrary, Haskell supports datatypes that hold types as elements,
although limited to types without term indices, but Nax does not.
The heterogeneous list datatype (|HList|) in Fig.\;\ref{fig:hlist}
is a well-known example that makes use of datatypes containing types.
Note that |HList| is index by |List{-"\;"-}*|, which is a promoted
regular list whose elements are of kind |*| (\ie, element are types).
For instance, |hlist| in Fig.\;\ref{fig:hlist} contains
three elements |3 : Int|, |True : Bool|, and |(1 :.2 :. Nil) : List Int|,
and it has type |HList (Int :. Bool :. List Int :. Nil)|.

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

\subsection{Singleton types} \label{ssec:singleton}
TODO

\subsection{Kind polymorphism} \label{ssec:kindpoly}
TODO


