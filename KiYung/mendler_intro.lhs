%include includelhs2tex.lhs


%format kappa = "\kappa"
%format Mu_kappa = Mu"_{"kappa"}"
%format Mu_star = Mu"_{"*"}"
%format Mu_star2star = Mu"_{"*"\to"*"}"
%format Mu_star2star2star = Mu"_{"*"\to"*"\to"*"}"
%format In_star2star2star = In"_{"*"\to"*"\to"*"}"
%format out_star2star2star = out"_{"*"\to"*"\to"*"}"

\section{Introduction}\label{sec:intro}
\index{fold}
\index{catamorphism}
\index{iteration}
\index{Mendler style}
\index{dependent type}
\index{higher-rank polymorphism}
The functional programming
community has traditionally focused on a style of recursion combinators that
works well in Hindley--Milner languages. One well-known combinator is called
fold (\aka\ catamorphism or iteration).
We explore a more expressive style called Mendler style.
Mendler-style recursion combinators were
originally developed in the context of the Nuprl \cite{Con86} type system.
Nuprl made extensive use of dependent types and higher-rank polymorphism.
General type checking in Nuprl was done by interactive theorem proving --
not by type inference. Mendler-style combinators are considerably more
expressive than the conventional combinators of the Squiggol \cite{AoP} school
in two aspects: (1) Mendler-style combinators are well behaved (\ie, they
guarantee termination) over a wider range of recursive datatypes
and (2) Mendler-style combinators are uniformly defined over
non-regular datatypes. An historical perspective on Mendler style
is summarized in \S\ref{mendler_history}.

Recently, Mendler-style recursion combinators have been studied
in the context of modern functional languages with advanced type system
features, including higher-rank polymorphism and
generalized algebraic datatypes.
This chapter extends that work by \vspace*{-.5em}
\begin{itemize}

\item[$\bigstar\!\!$] Illustrating that Mendler-style approach applies 
to useful examples of negative datatypes, through case studies on HOAS
(\S\ref{sec:showHOAS} and \S\ref{sec:evalHOAS}),\vspace*{-.2em}
\item[$\bigstar\!\!$] Extending Mendler-style iteration by using
the inverse trick (|msfcata|) (\S\ref{sec:showHOAS}),
which was first described by \citet{FegShe96}
and later refined by \citet{bgb} in conventional style,
\item[$\bigstar\!\!$] Using |msfcata| over an indexed datatype
to evaluate a simply-typed HOAS (\S\ref{sec:evalHOAS}), which clearly
exemplifies the advantages of Mendler style over conventional style,
\vspace*{-.2em}
\item Providing an intuitive explanation of why Mendler-style iteration
ensures termination (\S\ref{ssec:tourCata0})
even for negative datatypes (\S\ref{ssec:tourNegative}).
We illustrate a semi-formal proof of termination by encoding 
|msfcata| in the \Fw\ fragment of Haskell
(Figure \ref{fig:proof} in \S\ref{sec:proof}), %% \S\ref{sec:concl}
\vspace*{-.2em}
\item[$\bigstar\!\!$] Providing an intuitive explanation of
why Mendler-style course-of-values iteration
terminates for positive datatypes (\S\ref{ssec:tourHist0}),
but may fail to terminate for negative datatypes
(\S\ref{ssec:tourNegative}), by illustrating a counter-example that
obviously fails to terminate,
\vspace*{-.2em}
\item Organizing a large class of Mendler-style recursion combinators into
an intuitive hierarchy, of increasing generality, that is expressive enough
to cover regular datatypes (\S\ref{ssec:tourRegular}, \S\ref{ssec:tourHist0}),
nested datatypes (\S\ref{ssec:tourNested}),
indexed datatypes (GADTs) (\S\ref{ssec:tourIndexed}),
mutually recursive datatypes (\S\ref{ssec:tourMutRec}),
and negative datatypes (\S\ref{ssec:tourNegative}, \S\ref{sec:showHOAS}), and
\vspace*{-.2em}
\item 
Providing a detailed set of examples, all written in Haskell,
illustrating two versions (one with general recursion and one with
a Mendler-style recursion combinator) side by side, in order to
illustrate the usage of each family of recursion combinators.
\end{itemize}
\vspace*{-.5em}
The $\bigstar$-items are original contributions, and
the others are collective observations of common patterns
arising from the study of both previously known combinators and
our new combinators.

In this chapter, we demonstrate the Mendler-style combinators
in the Glasgow Haskell Compiler \cite{GHCuserguide} (GHC) dialect of Haskell.
However, this demonstration depends on a set of conventions, because we want
to control the source of non-termination. We assert that all our code fragments
conform with our conventions. These conventions include:
\begin{enumerate}
\item all values of algebraic datatypes are finite
    (\ie, do not use laziness to build infinite structures),
\item certain conventions of data abstraction that are not enforced by Haskell
    (\ie, treating the recursive type operator $\mu$,
	and the recursion combinators, as primitive constructs,
	rather than user-defined constructs), and
\item other sources of non-termination are delineated 
    (\eg, not allowed to use general recursion in user-defined datatypes
	and functions, pattern matching can only be done through
	the recursion combinators).
\end{enumerate}
\index{two-level type}
Mendler-style combinators operate on types defined in two levels,
\ie, two-level types (see \S\ref{ssec:tourRegular}). Two-level types are 
characterized by splitting the definition of a recursive type into
a generating functor (or a base datatype) and an explicit application of
the appropriate datatype fixpoint operator (|Mu|).
\index{fixpoint}
There exists
an infinite series of datatype fixpoint operators for each different kind
(\eg, |Mu0|, |Mu1|). In this chapter, we illustrate the Mendler-style
recursion combinators only at the two simplest kinds, $*$ and $* -> *$.

\subsection{Background - Termination and Negativity}\label{sec:mendler:motiv}
\citet{Mendler87} showed that diverging computations can be expressed using
recursive datatypes with negative occurrences of the datatype being defined. 
No explicit recursion at the value level is required to elicit non-termination.
We can illustrate this in Haskell as follows:
\begin{center}
\begin{tabular}{l||l}
\begin{minipage}{.5\linewidth}
\begin{code}
data T = C (T -> ())
p::T->(T->())
p (C f) = f
w :: T -> ()
w x = (p x) x
\end{code}
\end{minipage} &
\begin{minipage}{.4\linewidth}
\begin{code}
    w (C w)
~>  (p (C w)) (C w))
~>  w (C w)
~>  (p (C w)) (C w))
~>  {-"\cdots"-}
\end{code}
\end{minipage}
\end{tabular}
\end{center}
\index{datatype!negative}
On the left is a data definition of the negative datatype |T|
and the non-recursive functions |p| and |q|.
On the right is a diverging computation (|~>| denotes reduction steps).

Note the term |w (C w) :: T| diverges even though the functions |p| and |w| are
non-recursive. The cause of this divergence can be attributed to the ``hidden"
self application in the term |w (C w) :: T|. The negative occurrence of |T| in
the datatype definition of |T| is what enables this self application to be well
typed.

For this reason, many systems (\eg, Hagino's CPL \cite{hagino87phd} and
Coq \cite{P-M93}) require all recursive datatypes to be positive (or covariant)
in order to ensure normalization. \citet{UusVen99} call this style,
limiting recursive occurrences to positive positions,
the \emph{conventional} style, in contrast to what they name
Mendler style \cite{Mendler91}.  

In Mendler style, datatypes are not limited to recurse over
positive occurrences, yet functions expressible via iteration (\aka\ 
catamorphism) always terminate. This was first reported by \citet{uustalu98phd}
and \citet{matthes98phd}, but the search for exciting examples of
negative datatypes was postponed
(considering it ``may have a theoretical value only''\cite{UusVen99}).
Subsequent work \cite{UusVen00,vene00phd, AbeMatUus03, AbeMatUus05}, that
pioneered Mendler style in practical functional programming
also failed to produce good examples that make use of negative datatypes
in Mendler style.

\index{negative datatype}
\index{datatype!negative}
\index{datatype!mixed-variant}
In the functional programming community, there are both well-known and useful
examples of negative (or mixed-variant) datatypes
(\eg, delimited control\cite{Sha07}\footnote{
A Haskell datatype definition for this can be found at\\$~~~$
{\small \url{http://lists.seas.upenn.edu/pipermail/types-list/2004/000267.html}}}).
\index{HOAS}
One of the classic examples is HOAS \cite{Church40,PfeEll88}.
A non-standard definition of HOAS in Haskell is:\footnote{
The datatype |Exp| here is a HOAS-like structure specialized to |String| type.
The standard definition of HOAS, which omits the |Var| constructor, makes it
more challenging to define |showExp|, as we shall see in \S\ref{sec:showHOAS}.}
|data Exp = Lam (Exp -> Exp) || App Exp Exp || Var String|.
We can define a function |showExp{-"~"-}:: Exp -> String| that formats
an HOAS expression into a string.  For example,\vspace*{.3em}
\begin{code}
showExp (Lam (\x -> x))             ~> "(\a->a)"
showExp (Lam (\x -> App x x))       ~> "(\a->(a a))"
\end{code}\vspace*{-.7em}\\
The function |showExp| is total, provided the function values embedded in
the |Lam| data constructor are total.  We will illustrate that this example
(which involves a negative datatype) and many other examples that involve
non-regular datatypes and mutually recursive datatypes can all be easily
written using Mendler-style recursion combinators, whose termination
properties are known. A Detailed case study of how to express this function
using our Mendler-style iteration extended with syntactic inverses
is presented in \S\ref{sec:showHOAS}.

\subsection{Historical progression}\label{mendler_history}
\citet{Mendler87} discovered an interesting way of formalizing
primitive recursion, which was later dubbed ``Mendler style'',
while he was formalizing a logic that extended System \textsf{F} with
primitive recursion. Interestingly, Mendler did not seem to notice
(or maybe just did not bother to mention) that his style of formalizing
primitive recursion also guaranteed normalization for non-positive recursive
types -- Mendler required recursive types to be positive in his extension of
System \textsf{F}. A decade later, \citet{matthes98phd} and \citet{uustalu98phd}
noticed that Mendler never used the positivity condition in his proof of
strong normalization.

\index{Mendler-style!primitive recursion}
\citet{AbeMat04} generalized Mendler's primitive recursion combinator
\cite{Mendler87} into a family of combinators that are uniformly defined for
type constructors of arbitrary kinds. This was necessary for
handling nested datatypes. Their system extends System \Fw\ 
(\citet{Mendler87} extends System \textsf{F}). The notion
of a kind indexed family of Mendler combinators has now become the norm.

\index{termination!Mendler-style primitive recursion}
\index{strong normalization!MRec@@\textsf{MRec}}
\citet{AbeMat04} proved strong normalization of their language \textsf{MRec},
which extends System \Fw\ by adding a family of kind-indexed Mendler-style
primitive recursion combinators. They showed that \textsf{MRec} has
a reduction preserving embedding into a calculus they called \Fixw.
Then, they showed that \Fixw\ is strongly normalizing.
\index{System Fw@@System \Fw}
\index{System Fixw@@System \Fixw}

\index{Mendler-style!iteration}
Abel, Matthes, and Uustalu \cite{AbeMatUus03,AbeMatUus05} studied
a kind-indexed family of iteration combinators, along with examples
involving nested datatypes that make use of those combinators.
Iteration (\aka\ catamorphism) is a recursion scheme that has the same
computational power as primitive recursion (\ie, both can be defined
in terms of each other), but has different algorithmic complexity. 

\index{Mendler-style!primitive recursion}
It is strongly believed that primitive recursion is more efficient than
iteration. For instance, it is trivial to define a constant time predecessor
for natural numbers with primitive recursion, but it is believed impossible
to define the constant time predecessor with iteration. The Mendler-style
iteration family can be embedded into \Fw\ in a reduction preserving manner.
That is, we can encode the family of Mendler-style iteration combinators
into \Fw\ in such a way that the number of reduction steps of the original
and the embedding differ only by a constant number of steps. The primitive
recursion family, in contrast, is not believed to have a reduction preserving
embedding into \Fw. \citet{AbeMat04} needed a more involved embedding of
\textsf{MRec} into \Fixw, which has a richer structure than \Fw.

Although Matthes, Uustalu, and others were well aware of the fact that
the Mendler-style iteration family and the primitive recursion family both
normalize for negative recursive types, they did not explore or document actual
examples. They postponed ``the search for exciting examples of negative
recursive types". They stated that the normalization of negative types
``may have a theoretical value only''\cite{UusVen99}. So, until recently,
the study of Mendler-style recursion combinators has focused on examples of
positive recursive types possibly with type indices (but not term-indices).

Recently, we developed several new contributions to the study of
the Mendler-style recursion schemes \cite{AhnShe11}.\footnote{
	This chapter is a revised and extended version of this ICFP paper.}
These contributions fall into three broad categories:\vspace*{-.5em}
\begin{itemize}
\item discovered a new family of Mendler-style recursion combinators
 (\S\ref{sec:msf}), which normalizes for negative recursive types and
 is believed to be more expressive than the Mendler-style iteration family,
\item discovered a counterexample, which proves that some families of
 Mendler-style recursion combinators do not normalize for negative datatypes
 but only normalize for positive datatypes (\S\ref{ssec:tourNegative}), and
\item explored the use of Mendler-style recursion combinators over (almost)
 term-indexed types (\ie, GADTs) (\S\ref{ssec:tourIndexed}).
\end{itemize}
%% Details of these contributions are discussed in \S\ref{sec:msf},
%% \S\ref{ssec:tourHist0},\S\ref{sec:mgadt}), which are extended and
%% revised versions of the sections appearing in our recent work \cite{AhnShe11}.


\subsection{Roadmap to a tour of the Mendler-style approach}\label{sec:tour}
%include mendler/RecComb.lhs

In this subsection, we give an overview of the Mendler-style approach,
to orient the reader to navigate the following sections.

\index{regular datatype}
\index{datatype!regular}
\index{catamorphism}
\index{histomorphism}
First, we introduce the Mendler-style iteration (|mcata|. \aka\ catamorphism)
(\S\ref{ssec:tourCata0}) and course-of-values iteration
(|mhist|. \aka\ histomorphism) (\S\ref{ssec:tourHist0}) combinators at kind $*$,
that is, for (non-mutually recursive) regular datatypes
(\S\ref{ssec:tourRegular}). We also give
an intuitive explanation why these Mendler-style recursion combinators
ensure termination for positive datatypes.

\index{datatype!negative}
In \S\ref{ssec:tourNegative}, we discuss why the Mendler-style iteration
(|mcata|) ensures termination even for negative datatypes, while
the Mendler-style course-of-values iteration (|mhist|) can only ensure
termination for positive datatypes.

\index{datatype!nested}
Then, we move our focus from non-mutually recursive regular datatypes
to more expressive datatypes (\S\ref{mendler_nonreg}), which require
recursion combinators at kind $* -> *$. We provide several examples of
non-regular datatypes including nested datatypes (\S\ref{ssec:tourNested})
and indexed datatypes (GADTs) (\S\ref{ssec:tourIndexed}), which illustrate
the use of the Mendler-style iteration (|mcata|) and course-of-values
iteration (|mhist|) at kind $* -> *$. We also provide some examples that
show how to encode mutually recursive datatypes using indexed datatypes
(\S\ref{ssec:tourMutRec}).

\index{Mendler-style!primitive recursion}
In \S\ref{sec:mpr}, we introduce the Mendler-style primitive recursion (|mprim|)
and course-of-values recursion (|mcvpr|). These two combinators
|mprim| and |mcvpr| are equivalent to |mcata| and |mhist|, respectively,
in terms of computability, but often lead to more efficient implementations.

In \S\ref{sec:msf}, we introduce a new Mendler-style family (|msfcata|),
which we discovered, and illustrate its expressiveness over negative datatypes
by presenting the case study on formatting HOAS (\S\ref{sec:showHOAS})
and evaluating simply-typed HOAS (\S\ref{sec:evalHOAS})

Finally, we summarize the properties of Mendler-style recursion combinators
in \S\ref{sec:proof}. %% and extrapolate on other possible recursion combinators.



%%%% maybe it is better not to use 1st 2nd ....

\afterpage{
\begin{landscape}
\begin{figure}
\DataFix
\caption{Standard (|Mu|) and inverse-augmented (|Rec|) datatype fixpoints
at kinds $*$ and $* -> *$.}
\label{fig:datafix}
\end{figure}

\begin{figure}
{\small\TypesOfRecursiveCombinators }
\caption{Type signatures of recursion combinators.
         Note the heavy use of higher-rank types.}
\label{fig:rcombty}
\end{figure}

\begin{figure}
{\small \DefsOfRecursiveCombinators }
\caption[Definitions of recursion combinators.]{
	Definitions of recursion combinators.
	Note the identical textual definitions of
	the same operators at different kinds,
	but with types specialized for that kind.}
\label{fig:rcombdef}
\end{figure}
\end{landscape}
}

\index{fixpoint!standard}
All of our results are summarized in Figures \ref{fig:datafix},
\ref{fig:rcombty}, and \ref{fig:rcombdef}. In Figure \ref{fig:datafix},
we define the Mendler-style datatype fixpoint operators (\ie, |Mu0| and |Mu1|).
These are datatype definitions in Haskell that take type constructors
as arguments. They are used to tie the recursive knot
through the generating functor (or base datatype) that they take as an argument.

In Figure \ref{fig:rcombty}, we provide the types of 8 Mendler-style
combinators distributed over the two kinds that we consider,
along with the type of a conventional iteration combinator for comparison.
The combinators can be organized into a hierarchy of increasing generality.
By juxtaposing the types of the combinators, it looks clear
where in the hierarchy each combinator appears and
how each is related to the others.

In Figure \ref{fig:rcombdef}, we define the combinators themselves,
again distributed over two kinds. The definitions of the corresponding
combinators at two kinds are textually identical, although they
must be given different types at each kind.

In addition to the Mendler-style recursion combinators
in Figures \ref{fig:rcombty} and \ref{fig:rcombdef}, we introduce
Mendler-style primitive recursion (\MPr) and course-of-values recursion (\McvPr)
in \S\ref{sec:mpr}.

In Figures \ref{fig:len}, \ref{fig:fib}, \ref{fig:bsum}, \ref{fig:vec}, and
\ref{fig:mutrec}, we provide examples\footnote{Some of the examples
	(Figures \ref{fig:len}, \ref{fig:fib}, and \ref{fig:bsum}) are
	adopted from \cite{UusVen00,vene00phd,AbeMatUus03,AbeMatUus05}.}
selected for each of the combinators |mcata0|, |mhist0|, |mcata1|, and |mhist1|.
We provide examples using the \MPr\ and \McvPr\ families in \S\ref{sec:mpr}.
We discuss the remaining combinators of the inverse-augmented fixpoints
in \S\ref{sec:showHOAS} and \S\ref{sec:evalHOAS}, where we culminate with
examples involving HOAS.
\index{fixpoint!inverse-augmented}
We have structured each of the examples into two, side by side, parts.
On the left, we provide a general recursive version and
on the right, a Mendler-style version.

