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

In this section we introduce a generic |Path| datatype.
We will instantiate |Path| into three different types of
lists --  plain lists, length indexed lists 
(|List'| and |Vec| in Fig.\;\ref{fig:glist})
and a |Code| type, in order to write a stack safe compiler
(Fig.\;\ref{fig:compile}).

We will explain Fig.\;\ref{fig:glist} by discussing the Nax code.
The type constructor |Path| expects three arguments,
that is, |Path x {i} {j} : *|.  The argument |x : {iota} -> {iota} -> *|
is binary relation describing legal transitions (i.e. |x {i} {j}| is inhabited
if one can legally step from |i| to |j|).
The arguments |i : iota| and |j : iota| represent the initial and
final vertices of the |Path|. A term of type |Path x {i} {j}| witnesses
a path from |i| to |j| following the legal transition
steps given by the relation |x : {iota} -> {iota} -> *|. 

The |Path| datatype provides two ways of constructing witness paths.
Firstly, |pNil : Path x {i} {i}| witnesses an empty path (or,
$\epsilon$-transition) from a vertex to itself, which always exists
regardless of the choice of |x|.
Secondly, |pCons : x {i} {j} -> Path x {j} {k} -> Path x {i} {k}| witnesses
a path from |i| to |k|, provided that there is a single step transition from
|i| to |j| and that there exists path from |j| to |k|.

The function |append : Path x {i} {j} -> Path x {j} {k} -> Path x {i} {k}|
witnesses that there exists a path from |i| to |i| provided that
there exists a path from |i| to |j| and a path from |j| to |k|.
Note that the implementation of |append| is exactly the same as
the usual append function for plain lists.

We instantiate |Path| by providing a specific relation to the parameter |x|.

Plain regular lists (|List' a|) are path obnoxious. That is, one can always
add an element (|a|) to a list (|List' a|) to get a new list (|List' a|).
We instantiate |x| to a degenerate relation over a singleton set
|(Elem a) : Unit -> Unit -> *|, which is tagged by a value of type |a|.
Then, we can define |List' a| as a synonym of |Path (Elem a) Unit Unit|,
and their constructors |nil'| and |cons'|.

Since length indexed lists (|Vec a {n}|) need countably many configurations
representing length of the list. So, we instantiate |x| to relation over
natural numbers |(ElemV a): Nat -> Nat -> *| tagged by a value of type |a|.
The relation (|ElemV a|) counts down one step from |succ n| to |n|,
as described in the type signature of |MkElemV : a -> Elem a {`succ n} {n}|.
Then, we define |Vec a {n}| as a synonym |Path (ElemV a) {n} {`zero}|,
counting down from |n| to |zero|. In Nax, backquoted identifiers appearing
inside index terms enclosed by braces refer to the predefined names without
the backquote. (\eg, |`zero| appearing in |{`zero}| refers to the predefined
|zero : Nat|).

For plain lists and vectors, the relations (|Elem a| and |ElemV a|)
are independent of the value of type |a| they contain. That is, the transition
step for adding one value to a list is always the same regardless of the value.
Note that each of |Elem| and |ElemV| has only one data constructor
|MkElem| and |MkElemV|, respectively. In the following subsection, we will
instantiate |Path| with a relation for stack configurations that specifies
several different transition rules for different machine instruction values.

Haskell code is pretty much similar to the Nax code, except that it uses
general recursion and kinds are not explicitly annotated on datatypes.\footnote{
	In Haskell, kinds are inferred by default.
	The \texttt{KindSignatures} extension in GHC allows kind annotations.}
In Agda, there is no need to define wrapper datatypes like |Elem| and |ElemV|
since we can use type level functions no different from term level functions.

