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

Nax

|GList| expects three arguments: a binary relation |x| over indices and 
a pair of indices |i| and |j|.

path

Relation
possible transitions
edges

