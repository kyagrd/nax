%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{TODO main example}

\subsection{Type preserving evaluator for an expression language}
In a language that supports term-indices, we can write a type preserving
evaluator in three steps: (1) define the object language as a datatype
indexed by its type universe; (2) define the value as a datatype indexed
by the same type universe; and (3) write an evaluator that preserves the
term indices representing the object language type. Once the evaluator
type checks, we can be confident that our evaluator is type preserving,
relying on the type preservation property of the host language type system.

Our object language in Fig.\,\ref{fig:eval} is a simple expression language
(|Expr|) whose type universe (|Ty|) only consists of numbers (represented by
the constant term |I|) and booleans (represented by the constant term |B|).
We want to evaluate an expression to a value, which may be either numeric
(|IV n|) or boolean (|BV b|). Note that the value datatype (|Val|) is
indexed by constant terms (|I| and |B|) of the type universe (|Ty|).

An expression is either a value (|VAL v|), a numeric addition (|PLUS e1 e2|),
or a conditional (|IF e0 e1 e2|). The expression datatype (|Expr|) is also
indexed by the type universe (|Ty|). Note that the term indices used in
the definition |Expr| ensures that expressions are type correct by construction.
For instance, a conditional expression |IF e0 e1 e2| can only be constructed
when |e0| is a boolean expression (\ie, indexed by |B|) and
|e1| and |e2| are expressions of the same type (\ie, both indexed by |t|).

Then, we can write the evaluator (|eval|) from expressions to values, which
preserves the index that represents the object language type. The definition
of |eval| is fairly straightforward, since our expression language is a very
simple one. What we really want to focus on is the comparative understanding
of how term indices are treated in Nax, in comparison to how they are treated
in Haskell and Agda.

\subsection{Generic indexed lists parametrized by a binary relation}
TODO

\subsection{Stack-safe compiler for the expression language}

\afterpage{
\begin{landscape}
\begin{figure}
~~\qquad\qquad\,\textcolor{gray}{\texttt{GADTs},}
\\\vskip-5ex
\hspace*{-6ex}
\begin{minipage}{.31\linewidth}\input{exEvalHs}\end{minipage}
\begin{minipage}{.35\linewidth}\input{exEvalNax}\end{minipage}
\begin{minipage}{.33\linewidth}\input{exEvalAgda}\end{minipage}
\caption{A type preserving evaluator (|eval|) that evaluates
	an expression (|Expr|) to a value (|Val|).}
\label{fig:eval}
\end{figure}

\begin{figure}
\hspace*{-10ex}
\begin{minipage}{.3\linewidth}\input{exGListHs}\end{minipage}
\begin{minipage}{.355\linewidth}\input{exGListNax}\end{minipage}
\begin{minipage}{.345\linewidth}\input{exGListAgda}\end{minipage} \\
\hspace*{-10ex}
\begin{minipage}{.3\linewidth}\input{exGListHsEx}\end{minipage}
\begin{minipage}{.39\linewidth}\input{exGListNaxEx}\end{minipage}
\begin{minipage}{.33\linewidth}\input{exGListAgdaEx}\end{minipage}
\caption{A generic indexed list (|GList|) parameterized by
	a binary relation (|x|, |X|) over indices (|i,j,k|)
	and its instantiations (|List|, |Vec|).}
\label{fig:glist}
\end{figure}

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
