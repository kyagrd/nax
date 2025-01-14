\subsection{Type preserving evaluator for an expression language}
\label{ssec:eval}
\afterpage{
\begin{landscape}
\begin{figure}
~~\qquad\qquad\,\textcolor{gray}{\texttt{GADTs},}
\\\vskip-5ex
\hspace*{-6ex}
\begin{minipage}{.31\linewidth}\input{exEvalHs}\end{minipage}
\begin{minipage}{.35\linewidth}\input{exEvalNax}\end{minipage}
\begin{minipage}{.33\linewidth}\input{exEvalAgda}\end{minipage}
\caption{A type-preserving evaluator (|eval|) that evaluates
	an expression (|Expr|) to a value (|Val|).}\vskip1.5ex
\hspace{33ex}\begin{minipage}{.6\linewidth}
Curly braces in the Nax code above indicates the use of term indices in types.
For instance, |t| appearing in |{ t }| is a term-index variable rather than
a type variable.
\end{minipage}
\label{fig:eval}
\end{figure}
\end{landscape}
} % end afterpage

In a language that supports term-indices, one writes a type-preserving
evaluator as follows: (1) define a datatype TypeUniverse which encodes
types of the object language; (2) define a datatype Value (the range of
object language evaluation) indexed by terms of the type TypeUniverse;
(3) define a datatype ObjectLanguage indexed by the same type TypeUniverse;
and (4) write the evaluator (from expressions to values) that preserves
the term indices representing the type of the object language.
Once the evaluator type checks, we are confident that the evaluator is
type-preserving, relying on type preservation of the host-language type system.
In Fig.\,\ref{fig:eval}, we provide a concrete example of such
a type-preserving evaluator for a very simple expression language (|Expr|).

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

