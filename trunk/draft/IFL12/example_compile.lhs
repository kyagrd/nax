\subsection{Stack safe compiler for the expression language}
\label{ssec:compile}
\afterpage{
\begin{landscape}
\begin{figure}
\;\;~\;\;\textcolor{gray}{\texttt{KindSignatures}, \texttt{TypeOperators},}
\\\vskip-5ex
\hspace*{-10ex}
\begin{minipage}{.33\linewidth}\input{exCmplHs}\end{minipage}
\begin{minipage}{.40\linewidth}\input{exCmplNax}\end{minipage}
\begin{minipage}{.33\linewidth}\input{exCmplAgda}\end{minipage}
\caption{A stack-safe compiler}
\label{fig:compile}
\end{figure}
\end{landscape}
} % end afterpage

The stack safe compiler for the |Expr| language
more interesting use of 
The type preserving evaluator in Fig.\;\ref{fig:eval} is an index preserving
program where the index of the input type and the result type are just
the same.
