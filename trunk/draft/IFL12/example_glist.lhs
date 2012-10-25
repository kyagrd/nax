\subsection{Generic indexed lists parametrized by a binary relation}

\afterpage{
\begin{landscape}
\begin{figure}
\vskip-7.3ex
\hspace*{-10ex}
\begin{minipage}{.3\linewidth}\input{exGListHs}\end{minipage}
\begin{minipage}{.355\linewidth}\input{exGListNax}\end{minipage}
\begin{minipage}{.345\linewidth}\input{exGListAgda}\end{minipage}
\vskip-4ex ~ \\
\hspace*{-10ex}
\begin{minipage}{.3\linewidth}\input{exGListHsEx}\end{minipage}
\begin{minipage}{.39\linewidth}\input{exGListNaxEx}\end{minipage}
\begin{minipage}{.33\linewidth}\input{exGListAgdaEx}\end{minipage}
\vskip-2ex
\caption{A generic indexed list (|GList|) parameterized by
	a binary relation (|x|, |X|) over indices (|i,j,k|)
	and its instantiations (|List'|, |Vec|).}
\label{fig:glist}
\end{figure}
\end{landscape}
} % end afterpage

The |GList| datatype is a generic list structure that can be instantiated
into many different types of indexed lists. For example, |GList| can be
instantiate into plain regular lists (|List'|) and length indexed lists (|Vec|)
as illustrated in Fig.\;\ref{fig:glist}. Later on, in Fig.\;\ref{fig:compile},
we will instantiate |GList| into the |Code| type in order to write a stack safe
compiler.

|GList| expects three arguments to become a type,
that is, |GList x {i} {j} : *|. The binary relation |x : iota -> iota -> *|
gives defines possible transitions (or, edges of a graph)
and |i : iota| and |j : iota| represent initial and final configurations
(or, two vertices in a graph).  A term of type |GList x {i} {j}| witnesses
that there exists a path from |i| to |j| following the possible transition
steps given by the relation |x : iota -> iota -> *|. In other words,
(|i|, |j|) is in the reflexive transitive closure of |x|.

The |GList| datatype provides two ways of constructing witness for paths:

|gNil : GList x {i} {i}| witnesses an empty path (or, $\epsilon$-transition)
from vertex a to itself, which always exists regardless of the choice of |x|.

|gCons : x {i} {j} -> GList x {j} {k} -> GList x {i} {k}| witnesses that
there exists a path from |i| to |k|, provided that there is a single step
transition from |i| to |j| in |x| and that there exists path from |j| to |k|.

The function |append : GList x {i} {j} -> GList x {j} {k} -> GList x {i} {k}|
witnesses that there exists a path from |i| to |i| provided that
there exists a path from |i| to |j| and a path from |j| to |k|.
Note that the implementation of |append| is exactly the same as
plain regular lists.

To instantiate |GList| into a specific list-like structure, one instantiates
the parameter |x| to a specific relation. Since plain regular lists (|List' a|)
are path obnoxious, we instantiate |x| to a degenerate relation over
a singleton set |(Elem a) : Unit -> Unit -> *|, which is tagged by
a value of type |a|. Then, we define |List' a| as a synonym of
|GList (Elem a) Unit Unit|.
Since length indexed lists (|Vec a {n}|) needs
countably many configurations representing length of the list. So, we 
instantiate |x| to relation over natural numbers |(ElemV a): Nat -> Nat -> *|
tagged by a value of type |a|. The relation (|ElemV a|) counts down one step
from |succ n| to |n|.
Then, we define |Vec a {n}| as a synonym |GList (ElemV a) {n} {`zero}|,
counting down from |n| to |zero|. Backquote prefixed identifiers appearing
inside index terms enclosed by braces refer to the predefined names without
the backquote. (\eg, |`zero| appearing in |{`zero}| refers to the predefined
|zero : Nat|).

