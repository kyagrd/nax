\subsection{Generic |Path|s parametrized by a binary relation}
\label{ssec:glist}
\afterpage{
\begin{landscape}
\begin{figure}
\vskip-7.3ex
\qquad\quad\;\textcolor{gray}{\texttt{GADTs},}
\\\vskip-5.7ex
\hspace*{-10ex}
\begin{minipage}{.3\linewidth}\input{exGListHs}\end{minipage}
\begin{minipage}{.355\linewidth}\input{exGListNax}\end{minipage}
\begin{minipage}{.345\linewidth}\input{exGListAgda}\end{minipage}
\vskip-4ex ~ \\
\hspace*{-10ex}
\begin{minipage}{.3\linewidth}\input{exGListHsEx}\end{minipage}
\begin{minipage}{.355\linewidth}\input{exGListNaxEx}\end{minipage}
\begin{minipage}{.345\linewidth}\input{exGListAgdaEx}\end{minipage}
\vskip-2ex
\caption{A generic indexed list (|Path|) parameterized by
	a binary relation (|x|, |X|) over indices (|i,j,k|)
	and its instantiations (|List'|, |Vec|).}
\label{fig:glist}
\end{figure}
\end{landscape}
} % end afterpage

In this section we introduce a generic |Path| datatype.\footnote{
	There is a Haskell library package for this
	\url{http://hackage.haskell.org/package/thrist} }
We will instantiate |Path| into three different types of
lists --  plain lists, length indexed lists 
(|List'| and |Vec| in Fig.\;\ref{fig:glist})
and a |Code| type, in order to write a stack safe compiler
(Fig.\;\ref{fig:compile}).

%% We will explain Fig.\;\ref{fig:glist} by discussing the Nax code.
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

