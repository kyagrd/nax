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

explain in terms of Nax

|GList| expects three arguments to become a type,
that is, |GList x {i} {j} : *|. The binary relation |x : iota -> iota -> *|
gives defines possible transitions (or, edges of a graph)
and |i, j : \iota| represents initial and final configurations
(or, two vertices in a graph).  A term of type |GList x {i} {j}| witnesses
that there exists a path from |i| to |j| following the possible transition
steps given by the relation |x : iota -> iota -> *|. In other words,
(|i|, |j|) is in the reflexive transitive closure of |x|.

|gNil : GList x {i} {i}| witnesses an empty path (or, $\epsilon$-transition)
from vertex a to itself, which always exists regardless of the choice of |x|.

|gCons : x {i} {j} -> GList x {j} {k} -> GList x {i} {k}| witnesses that
there exists a path from |i| to |k|, provided that there is a single step
transition from |i| to |j| in |x| and that there exists path from |j| to |k|.

exists a trivial (or path

|append : GList x {i} {j} -> GList x {j} {k} -> GList x {i} {k}|


Haskell is similar
Agda 
