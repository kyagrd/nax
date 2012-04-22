%include includelhs2tex.lhs


%format kappa = "\kappa"
%format Mu_kappa = Mu"_{"kappa"}"
%format Mu_star = Mu"_{"*"}"
%format Mu_star2star = Mu"_{"*"\to"*"}"
%format Mu_star2star2star = Mu"_{"*"\to"*"\to"*"}"
%format In_star2star2star = In"_{"*"\to"*"\to"*"}"
%format out_star2star2star = out"_{"*"\to"*"\to"*"}"

\section{Introduction}\label{sec:intro}

In this chapter, we explore a family of terminating recursion combinators
over a wide class of recursive datatypes. The functional programming
community has traditionally focused on families of combinators that work
well in Hindley-Milner languages, characterized by folds and catamorphisms
(\aka\ iterations). We explore a more expressive family called Mendler-style
combinators. The Mendler-style combinators were originally developed in
the context of the Nuprl \cite{Con86} type system.  Nuprl made extensive use
of dependent types.  General type checking in Nuprl was done by interactive
theorem proving --- not by type inference.  The Mendler-style combinators
are considerably more expressive than the conventional combinators of
the Squiggol \cite{AoP} school, in the sense that the Mendler-style combinators
are well-behaved (\ie, guarantee termination) over wider range of recursive
datatypes. Historical progression on the studies of the Mendler-style approach
is summarized in \S\ref{mendler_history}.

Recently, Mendler-style combinators have been studied in the context of
modern functional languages with advanced type system features, including
higher-rank polymorphism and generalized algebraic data types.
We extend those studiers by \vspace*{-.5em}
\begin{itemize}

\item[$\bigstar\!\!$] Illustrating that the Mendler-style approach applies 
to useful examples of negative datatypes,
through the case study of the HOAS formatting function (\S\ref{sec:showHOAS}).
\vspace*{-.2em}
\item[$\bigstar\!\!$] Extending the Mendler-style iteration by using
the inverse trick first described by \citet{FegShe96},
and later refined by \citet{bgb} (\S\ref{sec:showHOAS}).
\vspace*{-.2em}
\item Providing an intuitive explanation of why the Mendler-style iteration
ensures termination (\S\ref{ssec:tourCata0})
even for negative datatypes (\S\ref{ssec:tourNegative}).
We illustrate a semi-formal proof of termination by encoding 
the extended iteration in the $F_\omega$ fragment in Haskell
(Figure \ref{fig:proof}, \S\ref{sec:proof}). %% \S\ref{sec:concl}
\vspace*{-.2em}
\item[$\bigstar\!\!$] Providing an intuitive explanation of
why the Mendler-style course-of-values iteration
terminates for positive datatypes (\S\ref{ssec:tourHist0}),
but may fail to terminate for negative datatypes
(\S\ref{ssec:tourNegative}) by showing a counter-example to termination.
\vspace*{-.2em}
\item Organizing a large class of Mendler-style recursion combinators into
an intuitive hierarchy, of increasing generality, that is expressive enough
to cover regular dataypes (\S\ref{ssec:tourRegular}, \S\ref{ssec:tourHist0}),
nested datatypes (\S\ref{ssec:tourNested}),
indexed datatypes (GADTs) (\S\ref{ssec:tourIndexed}),
mutually recursive datatypes (\S\ref{ssec:tourMutRec}),
and negative datatypes (\S\ref{ssec:tourNegative}, \S\ref{sec:showHOAS}).
\vspace*{-.2em}
\item 
Providing a detailed set of examples, all written in Haskell,
in both the conventional and the Mendler style, in order to
illustrate the usage of each family of recursion combinators.

\end{itemize}
\vspace*{-.5em}
The $\bigstar$-items are original contributions, and
the others are collective observations of common patterns
arising from the study of both the previously known combinators and
our new combinators.

We demonstrate the Mendler-style combinators in the Glasgow Haskell Compiler
\cite{GHCuserguide} (GHC) dialect of Haskell. However, this demonstration
depends on a set of conventions.  We assert that all our code fragments
conform with our conventions. The conventions include:
\begin{enumerate}
\item all values of algebraic data types are finite
    (\ie, do not use lazyness to build infinite structure),
\item certain conventions of data abstraction not enforced by Haskell
    (\ie, treat recursive type operator $\mu$ and the recursion combinators
          as primitive constructs rather than user-defined constructs), and
\item other sources of nontermination are delineated 
    (\eg, not allowed to use general recursion in user-defined datatypes
          and functions).
\end{enumerate}
The motivation for this investigation is the design of Trellys, a
full-featured language with dependent types being developed by a
cooperative project of Portland State University, the University of Iowa,
and the University of Pennsylvania. A design goal of Trellys is to develop
an inference mechanism which determines what terms of the language are safe
to use as a logic, and what terms can only be used as programs. We call
this analysis {\em logicality inference}. The intent is that logical values
can be interpreted as proof objects by a Curry-Howard style interpretation,
while programmatic values are allowed to express arbitrary computations
(including non-termination). The usability of Trellys requires that it be
as expressive as possible over natural forms of inductive and recursive
argument.  Hence our motivation to fully understand the Mendler-style
recursion combinators. It is our intention that the three conventions
discussed in the previous paragraph will be enforced in the Trellys system, and
our use of Haskell to illustrate the Mendler style, will soon be unnecessary.

The use of Mendler-style combinators is characterized by splitting the
definition of a recursive type into a generating functor (or a base datatype)
and an explicit application of the appropriate datatype fixpoint operator.  
There exists an infinite series of datatype fixpoint operators for each
different kind. In this chapter we illustrate only the two simplest kinds
$*$ and $* -> *$. 


\subsection{Background - Termination and Negativity}\label{sec:motiv}
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
On the left is a data definition of the negative datatatpe |T|,
and the non-recursive functions |p| and |q|.
On the right is a diverging computation (|~>| denotes reduction steps).

Note, the term |w (C w) :: T| diverges even though the functions |p| and |w| are
non-recursive. The cause of this divergence can be attributed to the ``hidden"
self application in the term |w (C w) :: T|. The negative occurrence of |T| in
the datatype definition of |T| is what enables this self application to be well
typed.

For this reason, many systems (e.g., Hagino's CPL \cite{hagino87phd}, and
Coq \cite{P-M93}) require all recursive datatypes to be positive
(or covariant) in order to ensure normalization. \citet{UusVen99} call
this style, limiting recursive occurrences to positive positions,
the \emph{conventional} style, in contrast to what they name
the Mendler style \cite{Mendler91}.  

In the Mendler style, datatypes are not limited to recurse over
positive occurrences, yet functions expressible via iteration (\aka,
catamorphism) always terminate. This was first reported by \citet{uustalu98phd}
and \citet{matthes98phd}, but the search for exciting examples of
negative datatypes was postponed until another time
(considering it ``may have a theoretical value only''\cite{UusVen99}).
Subsequent work \cite{UusVen00,vene00phd, AbeMatUus03, AbeMatUus05}, that
pioneered the Mendler style in practical functional programming,
also failed to produce good examples that make use of negative datatypes
in the Mendler style.

In the functional programming community, there are both well-known and useful
examples of negative and mixed datatypes
(e.g., delimited control\cite{Sha07}\footnote{
A Haskell datatype definition for this can be found at\\$~~~$
{\tiny \url{http://lists.seas.upenn.edu/pipermail/types-list/2004/000267.html}}}).
One of the classic examples is Higher-Order Abstract Syntax (HOAS)
\cite{Church40,PfeEll88}. A non-standard definition of HOAS
in Haskell is:\footnote{
The standard definition of HOAS, which omits the |Var| constructor, makes it
more challenging to define |showExp|, as we shall see in \S\ref{sec:showHOAS}.}
\vspace*{.3em}
\begin{code}
{-"\!\!\!\!\!\!\!\!"-}data Exp = Lam (Exp -> Exp) | App Exp Exp | Var String
\end{code}\vspace*{-.7em}\\
We can define a function |showExp :: Exp -> String| that formats
an HOAS expression into a string.  For example,\vspace*{.3em}
\begin{code}
showExp (Lam (\x -> x))             ~> "(\a->a)"
showExp (Lam (\x -> App x x))       ~> "(\a->(a a))"
\end{code}\vspace*{-.7em}\\
The function |showExp| is total, provided the function values embedded in
the |Lam| data constructor are total (which is one of the things the Trellys'
logicality inference provides).  We will illustrates that this example
(a negative datatype), and many others examples including non-regular
datatypes and mutually recursive datatypes can all be easily written as
Mendler-style recursion, whose termination properties are known.
Detailed case study of how to express this function using our extended
Mendler-style iteration is presented in \S\ref{sec:showHOAS}.

\subsection{Historical progression}\label{mendler_history}
\citet{Mendler87} discovered an interesting way of formalizing
primitive recursion, which was later dubbed ``the Mendler-style'',
while he was formalizing a logic that extended System \textsf{F} with
primitive recursion. Interestingly, Mendler did not seem to notice
(or maybe, just did not bother to mention) that his style of formalizing
primitive recursion also guaranteed normalization for non-positive recursive
types -- Mendler required recursive types to be positive in his extension of
System \textsf{F}. A decade later, \citet{matthes98phd} and \citet{uustalu98phd}
noticed that Mendler never used the positivity condition in his proof of
strong normalization.

\citet{AbeMat04} generalized Mendler's primitive recursion combinator
\cite{Mendler87} into a family of combinators that are uniformly defined for
type constructors of arbitrary kinds. This was necessary for
handling nested datatypes. Their system extends System \Fw\ 
(\citet{Mendler87} extends System \textsf{F}). The notion
of a kind indexed family of Mendler combinators has now become the norm.

\citet{AbeMat04} prove strong normalization of their language \textsf{MRec},
which extends System \Fw\ by adding a family of kind-indexed Mendler-style
primitive recursion combinators. They show that \textsf{MRec} has
a reduction preserving embedding into a calculus they call \Fixw.
Then, they show that \Fixw\ is strongly normalizing.

Abel, Matthes, and Uustalu \cite{AbeMatUus03,AbeMatUus05} studied
a kind-indexed family of iteration combinators, along with examples
involving nested datatypes that make use of those combinators.
Iteration (\aka\ catamorphism) is a recursion scheme, which has the same
computational power as primitive recursion (\ie, both can be defined
in terms of each other), but has different algorithmic complexity. 

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

Although Matthes, Uustalu, and others, were well aware of the fact that
the Mendler-style iteration family and the primitive-recursion family both
normalize for negative recursive types, they did not explore or document actual
examples. They postponed ``the search for exciting examples of negative
recursive types" until another time. They stated that the normalization
of negative types ``may have a theoretical value
only''\cite{UusVen99}. So, until recently, the study on Mendler-style recursion
combinators focused on examples of positive recursive types with type
rather than term) based indexing.

Recently, I have developed several new contributions to the study of
the Mendler-style recursion shemes \cite{AhnShe11}. These contributions
fall into three broad categories:
\begin{itemize}
\item discovered a new family of Mendler-style recursion combinators,
	which normalizes for negative recursive types and is believed
	to be more expressive than the Mendler-style iteration family
	(\S\ref{sec:msf}),
\item discovered a counterexample, which proves that
	some families of Mendler-style recursion combinators
	do not normalize for negative recursive types
	but only normalize for positive recursive types (\S\ref{sec:mcv}), and
\item extended Mendler-style recursion combinators to (almost)
	term indexed types (\ie, Generalized Algebraic DataType(GADT)s)
	(\S\ref{sec:mgadt}).
\end{itemize}
Details of these contributions are discussed in the previous sections
(\S\ref{sec:msf},\S\ref{sec:mcv},\S\ref{sec:mgadt}), which are extended and
revised versions of the sections appearing in our recent work \cite{AhnShe11}.


\section{Roadmap to a tour of the Mendler-style approach}\label{sec:tour}
%include mendler/RecComb.lhs
%include mendler/CataViaHisto.lhs
%include mendler/Proof.lhs

In this section we give an overview of the Mendler-style approach,
to orient the reader to navigate the following sections.
First, we introduce both the iteration (\aka\ catamorphism)
(\S\ref{ssec:tourCata0}) and course-of-values iteration (\aka\ histomorpism)
(\S\ref{ssec:tourHist0}) combinators for kind $*$, that is,
for regular datatypes.
Second, we provide intuition why Mendler-style recursion combinators ensure
termination for positive datatypes. Third, we move our focus from
regular datatypes to more expressive datatypes which recursion combinators
for kind $* -> *$. These include nested datatypes (\S\ref{ssec:tourNested}),
indexed datatypes(GADTs) (\S\ref{ssec:tourIndexed}), and
mutually recursive datatypes (\S\ref{ssec:tourMutRec}).
Fourth, we give intuition why the Mendler-style iteration ensures
termination even for negative datatypes (\S\ref{ssec:tourNegative}).
Finally, we present the case study focusing on HOAS in \S\ref{sec:showHOAS}.

\afterpage{
\begin{landscape}
\begin{figure}
\DataFix
\caption{Standard (|Mu|) and inverse augmented (|Rec|) datatype fixpoints
 for kind $*$ and kind $* -> *$}
\label{fig:datafix}
\end{figure}

\begin{figure}
{\small\TypesOfRecursiveCombinators }
\caption{Type signatures of recursive combinators.
         Note the heavy use of higher-rank types.}
\label{fig:rcombty}
\end{figure}

\begin{figure}
{\small \DefsOfRecursiveCombinators }
\caption{Definitions of recursive combinators.
  Note identical textual definitions for the same operators at different kinds,
  but with types specialized for that kind.}
\label{fig:rcombdef}
\end{figure}
\end{landscape}
}

\begin{figure}
\CataViaHisto
\caption{\normalsize Alternative definition of iteration via course-of-values iteration.}
\label{fig:cataviahisto}
\end{figure}

\begin{figure}
\ProofCata
\caption{\normalsize $F_{\omega}$ encoding of |Mu0| and |mcata0| in Haskell}
\label{fig:proof}
\end{figure}

All of our results are summarized in Figures \ref{fig:datafix},
\ref{fig:rcombty}, and \ref{fig:rcombdef}. In Figure \ref{fig:datafix},
we define the Mendler-style datatype fixpoint operators (i.e. |Mu0| and |Mu1|).
These are datatype definitions in Haskell that take type constructors
as arguments. They are used to tie the recursive knot
through the generating functor (or base datatype) that they take as an argument.

In Figure \ref{fig:rcombty}, we provide the types of 8 Mendler-style
combinators distributed over the two kinds that we consider,
along with the type of a conventional iteration combinator for comparison.
The combinators can be organized into a hierarchy of increasing generality, and
juxtaposing the types of the combinators makes it clear where in the hierarchy
each combinator appears, and how each is related to the others.

In Figure \ref{fig:rcombdef}, we define the combinators themselves,
again distributed over two kinds. The definition of the corresponding
combinators in the two kinds are textually identical, although they
must be given different types in each kind.

In Figures \ref{fig:len}, \ref{fig:fib}, and \ref{fig:bsum}, \ref{fig:vec}, and
\ref{fig:mutrec}, we provide examples\footnote{Some of the examples
(Figures \ref{fig:len}, \ref{fig:fib}, and \ref{fig:bsum}) are
adopted from \cite{UusVen00,vene00phd,AbeMatUus03,AbeMatUus05}.}
selected for each of the combinators |mcata0|, |mhist0|, |mcata1|, and |mhist1|.
We discuss the remaining combinators of the inverse augmented fixpoints
in \S\ref{sec:showHOAS}, where we culminate with the HOAS formatting example.
We have structured each of the examples into two, side by side, parts.
On the left, we provide a general recursive encoding, and
on the right, a Mendler-style encoding.


