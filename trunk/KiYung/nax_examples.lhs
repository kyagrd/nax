\section{The trilingual Rosetta Stone}
\label{sec:example}

In this section, we introduce three examples
(Figs.\;\ref{fig:eval} and \ref{fig:evalCont},
 Figs.\;\ref{fig:glist} and \ref{fig:glistCont}, and
 Figs.\;\ref{fig:compile} and \ref{fig:compileCont})
that use term indexed datatypes to enforce program invariants.
Each example is written in three different languages
-- like the Rosetta Stone -- Haskell, Nax,  and Agda.
We have crafted these programs to look as similar as possible,
by choosing the same identifiers and syntax structure whenever
possible, so that anyone already familiar with Haskell-like languages
or Agda-like languages will understand our Nax programs
just by comparing them with the programs on the left and right.
The features unique to Nax are summarized in Table\;\ref{tbl:naxfeatures}.

The three examples we introduce are the following:
\begin{itemize}\vspace*{-.5ex}
\item A type-preserving evaluator for a simple expression language
(Sect. \ref{ssec:eval}),
\item A generic |Path| datatype that can be specialized to various
list-like structures with indices (Sect. \ref{ssec:glist}), and
\item A stack-safe compiler for the same simple expression language,
which uses the |Path| datatype (Sect. \ref{ssec:compile}).
\end{itemize}
We adopted the examples from Conor McBride's keynote talk \cite{McBride12}
at ICFP 2012 (originally written in Agda). All the example code was tested
in GHC 7.4.1 (should also work in later versions such as GHC 7.6.x),
our prototype Nax implementation, and Agda 2.3.0.1.

\subsection{Type preserving evaluator for an expression language}
\label{ssec:eval}

\begin{figure}
\,\;~~\,\qquad\textcolor{gray}{\texttt{GADTs},}\\ \vskip-7ex
\hspace*{-6ex}
\begin{minipage}{.48\linewidth}\small
%include IFL12code/Eval.lhs
\end{minipage}
\begin{minipage}{.48\linewidth}\small
%include IFL12code/Eval.lnax
\end{minipage}
\caption{A type-preserving evaluator (|eval|) that evaluates
	an expression (|Expr|) to a value (|Val|), in Haskell and in Nax}
\label{fig:eval}
\end{figure}

\begin{figure}
\hspace*{-6ex}
\begin{minipage}{.48\linewidth}\small
%include IFL12code/Eval.lnax
\end{minipage}
\begin{minipage}{.6\linewidth}\small
%include IFL12code/Eval.lagda
\end{minipage}
\caption{A type-preserving evaluator (|eval|) that evaluates
	an expression (|Expr|) to a value (|Val|), in Nax and in Agda}
\label{fig:evalCont}
\end{figure}


In a language that supports term-indices, one writes a type-preserving
evaluator as follows: (1) define a datatype TypeUniverse which encodes
types of the object language; (2) define a datatype Value (the range of
object language evaluation) indexed by terms of the type TypeUniverse;
(3) define a datatype ObjectLanguage indexed by the same type TypeUniverse;
and (4) write the evaluator (from expressions to values) that preserves
the term indices representing the type of the object language.
Once the evaluator type checks, we are confident that the evaluator is
type-preserving, relying on type preservation of the host-language type system.
In Figs.\;\ref{fig:eval} and \ref{fig:evalCont}, we provide a concrete example
of such a type-preserving evaluator for a very simple expression language
(|Expr|).

Our TypeUniverse (|Ty|) for the expression language consists of numbers and
booleans, represented by the constants |I| and |B|. We want to evaluate an
expression, to get a value, which may be either numeric (|IV n|) or boolean
(|BV b|).  Note that the both the |Expr| and |Val| datatypes are indexed by
constant terms (|I| and |B|) of TypeUniverse (|Ty|). The terms of TypeUniverse
are also known as \emph{type representations}.

An expression (|Expr|) is either a value (|VAL v|), a numeric addition
(|PLUS e1 e2|), or a conditional (|IF e0 e1 e2|).  Note that the term indices
of |Expr| ensure that expressions are type correct by construction.
For instance, a conditional expression |IF e0 e1 e2| can only be constructed
when |e0| is a boolean expression (\ie, indexed by |B|) and
|e1| and |e2| are expressions of the same type (\ie, both indexed by |t|).
Then, we can write an evaluator (|eval|) (from expressions to values) which
preserves the index that represents the object language type. The definition
of |eval| is fairly straightforward, since our expression language is a very
simple one. Note that the functions in Nax do not
need type annotations (they appear as comments in \textcolor{gray}{gray}).
In fact, Nax currently does not support any syntax for type annotations
on function declarations.

Curly braces in the Nax code above indicates the use of term indices in types.
For instance, |t| appearing in |{ t }| is a term-index variable rather than
a type variable.

\subsection{Generic |Path|s parametrized by a binary relation}
\label{ssec:glist}

\begin{figure}
\begin{singlespace}
\qquad~\,\textcolor{gray}{\texttt{GADTs},} \\ \vskip-5ex
\hspace*{-10ex}
\begin{minipage}{.50\linewidth}\small
\vskip-2.6ex
%include IFL12code/GList.lhs
\end{minipage}~
\begin{minipage}{.48\linewidth}\small
%include IFL12code/GList.lnax
\end{minipage}
\vskip-4ex ~ \\
\hspace*{-10ex}
\begin{minipage}{.50\linewidth}\small
%include IFL12code/GListExample.lhs
\end{minipage}~
\begin{minipage}{.48\linewidth}\small
%include IFL12code/GListExample.lnax
\end{minipage}
\end{singlespace}
\caption{A generic indexed list (|Path|) parameterized by
	a binary relation (|x|) over indices (|i,j,k|)
	and its instantiations (|List'|, |Vec|), in Haskell and in Nax.}
\label{fig:glist}
\end{figure}

\begin{figure}
\begin{singlespace}
\hspace*{-10ex}
\begin{minipage}{.55\linewidth}\small \vskip2ex
%include IFL12code/GList.lnax
\end{minipage}~
\begin{minipage}{.48\linewidth}\small
%include IFL12code/GList.lagda
\end{minipage}
\vskip-4ex ~ \\
\hspace*{-10ex}
\begin{minipage}{.55\linewidth}\small
%include IFL12code/GListExample.lnax
\end{minipage}~
\begin{minipage}{.48\linewidth}\small
%include IFL12code/GListExample.lagda
\end{minipage}
\end{singlespace}
\caption{A generic indexed list (|Path|) parameterized by
	a binary relation (|x|, |X|) over indices (|i,j,k|)
	and its instantiations (|List'|, |Vec|), in Nax and in Agda.}
\label{fig:glistCont}
\end{figure}


In this section we introduce a generic |Path| datatype.\footnote{
	There is a Haskell library package for this
	\url{http://hackage.haskell.org/package/thrist} }
We will instantiate |Path| into three different types of
lists --  plain lists, length indexed lists 
(|List'| and |Vec| in Figs.\;\ref{fig:glist} and \ref{fig:glistCont})
and a |Code| type, in order to write a stack-safe compiler
(Fig.\;\ref{fig:compile} and \ref{fig:compileCont}).

The type constructor |Path| expects three arguments,
that is, |Path x {i} {j} : *|.  The argument |x : {iota} -> {iota} -> *|
is binary relation describing legal transitions (i.e. |x {i} {j}| is inhabited
if one can legally step from |i| to |j|).
The arguments |i : iota| and |j : iota| represent the initial and
final vertices of the |Path|. A term of type |Path x {i} {j}| witnesses
a (possibly many step) path from |i| to |j| following the legal transition
steps given by the relation |x : {iota} -> {iota} -> *|. 

The |Path| datatype provides two ways of constructing witnesses of paths.
First, |pNil : Path x {i} {i}| witnesses an empty path (or,
$\epsilon$-transition) from a vertex to itself, which always exists
regardless of the choice of |x|.
Second, |pCons : x {i} {j} -> Path x {j} {k} -> Path x {i} {k}| witnesses
a path from |i| to |k|, provided that there is a single step transition from
|i| to |j| and that there exists a path from |j| to |k|.

The function |append : Path x {i} {j} -> Path x {j} {k} -> Path x {i} {k}|
witnesses that there exists a path from |i| to |k| provided that
there exist two paths from |i| to |j| and from |j| to |k|.
Note that the implementation of |append| is exactly the same as
the usual append function for plain lists.
We instantiate |Path| by providing a specific relation to 
instantiate the parameter |x|.

Plain lists (|List' a|) are path oblivious. That is, one can always
add an element (|a|) to a list (|List' a|) to get a new list (|List' a|).
We instantiate |x| to the degenerate relation
|(Elem a) : Unit -> Unit -> *|, which is tagged by a value of type |a|
and witnesses a step with no interesting information.
Then, we can define |List' a| as a synonym of |Path (Elem a) {U} {U}|,
and its constructors |nil'| and |cons'|.

Length indexed lists (|Vec a {n}|) need a natural number index to
represent the length of the list. So, we instantiate |x| to a relation over
natural numbers |(ElemV a): Nat -> Nat -> *| tagged by a value of type |a|
witnessing steps of size one.
The relation (|ElemV a|) counts down exactly one step, from |succ n| to |n|,
as described in the type signature of |MkElemV : a -> Elem a {`succ n} {n}|.
Then, we define |Vec a {n}| as a synonym |Path (ElemV a) {n} {`zero}|,
counting down from |n| to |zero|. In Nax, in a declaration, backquoted identifiers appearing
inside index terms enclosed by braces refer to functions or constants in the 
current scope
(\eg, |`zero| appearing in |Path (ElemV a) {n} {`zero}| refers to the predefined
|zero : Nat|). Names without backquotes (\eg, |n| and |a|) are implicitly universally quantified.

For plain lists and vectors, the relations, (|Elem a|) and (|ElemV a|),
are parameterized by the type |a|. That is, the transition
step for adding one value to the path is always the same,
independent of the value.
Note that both |Elem| and |ElemV| have only one data constructor
|MkElem| and |MkElemV|, respectively, since all ``small" steps
are the same. In the next subsection, we will
instantiate |Path| with a relation witnessing stack configurations,
with multiple constructors, each witnessing different transition 
steps for different machine instructions.

The Haskell code is similar to the Nax code, except that it uses
general recursion and kinds are not explicitly annotated on datatypes.\footnote{
	In Haskell, kinds are inferred by default.
	The \texttt{KindSignatures} extension in GHC allows kind annotations.}
In Agda, there is no need to define wrapper datatypes like |Elem| and |ElemV|
since type level functions are no different from term level functions.


\subsection{Stack safe compiler for the expression language}
\label{ssec:compile}

\begin{figure}
\textcolor{gray}{\small \texttt{KindSignatures}, \texttt{TypeOperators},}
\\\vskip-6ex
\hspace*{-10ex}
\begin{minipage}{.50\linewidth}\small
%include IFL12code/Compile.lhs
\end{minipage}
\begin{minipage}{.48\linewidth}\small
%include IFL12code/Compile.lnax
\end{minipage}
\caption{A stack-safe compiler, in Haskell and in Nax.}
\label{fig:compile}
\end{figure}

\begin{figure}
\hspace*{-10ex}
\begin{minipage}{.55\linewidth}\small
%include IFL12code/Compile.lnax
\end{minipage}~
\begin{minipage}{.48\linewidth}\small
%include IFL12code/Compile.lagda
\end{minipage}
\caption{A stack-safe compiler, in Nax and in Agda}
\label{fig:compileCont}
\end{figure}



In Figs.\;\ref{fig:compile} and \ref{fig:compileCont},
we implement a stack-safe compiler for the same expression language
(|Expr| in Figs.\;\ref{fig:eval} and \ref{fig:evalCont}) discussed in
Sect.\;\ref{ssec:eval}. In Fig.s\;\ref{fig:eval} and \ref{fig:evalCont} of
that section, we implemented an index preserving evaluator
|eval : Expr {t} -> Val {t}|. Here, the stack-safe compiler
|compile : Expr {t} -> Code {ts} {`cons t ts}| uses the index
to enforce stack safety -- an expression of type |t| compiles to some code,
which when run on a stack machine with an initial stack configuration |ts|,
terminates with the final stack configuration |cons t ts|.

A stack configuration is an abstraction of the stack 
that tracks only the types of the values stored there.
We represent a stack configuration as
a list of type representations (|List Ty|).\footnote{
	The astute reader may wonder why we use |List| instead of the already
	defined |List'| in Figs.\;\ref{fig:glist} and \ref{fig:glistCont},
	which is exactly the plain list we want. In Nax and Agda, it is possible
	to have term indices of |List' Ty| instead of |List Ty|. (In Nax and
	Agda, the |List| datatype is defined in their standard libraries.)
	Unfortunately, it is not the case in Haskell.
	Haskell's datatype promotion does not allow promoting datatypes
	indexed by the already promoted datatypes. Recall that |List' Ty| is
	a synonym of |Path (Elem Ty) () ()|, which cannot be promoted to
	an index since it is indexed by the already promoted unit term |()|.
	In the following section, we will discuss further on how
	the two approaches of Nax versus Haskell differ
	in their treatment of term indexed types.}
For instance, the configuration for the stack containing three values
(from top to bottom) [3, True, 4] is |cons I (cons B (cons I Nil))|.

To enforce stack safety, each instruction 
(|Inst : List Ty -> List Ty -> *|) is indexed with its initial and
final stack configuration. For example, |aDD : Inst {`cons I (`cons I ts)} {`cons I ts}|
instruction expects two numeric values on top of the stack. 
Running the |aDD| instruction will consume those two values,
replacing them with a new numeric value (the result of the addition)
 on top of the stack, leaving the rest of the stack unchanged.

We define |Code| as a |Path| of stack consistent instructions
(\ie, |Code {ts} {ts'}| is a synonym for |Path Inst {ts} {ts'}|
from Sect. \ref{ssec:glist}).
For example, the compiled code consisting of the three instructions
|inst1 : Inst {ts0} {ts1}|,
|inst2 : Inst {ts1} {ts2}|, and
|inst3 : Inst {ts2} {ts3}| has the type |Code {ts0} {ts3}|.
 

