%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{TODO main example}

a type preserving evaluator and a stack safe compiler for a simple expression
lagnauge.

\subsection{Type preserving evaluator for an expression language}
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
\end{landscape}
} % end afterpage

In a language that supports term-indices, we can write a type preserving
evaluator as follows: (1) define a type universe for the object language
as a datatype; (2) define values (into which the object language will evaluate)
as a datatype indexed by terms of the type universe; (3) define the object
language as a datatype indexed by the same type universe; and (4) write
an evaluator from expressions to values such that it preserves the term indices
representing type of the object language. Once the evaluator type checks,
we can be confident that the evaluator is type preserving, relying on
the type preservation property of the host language type system.
In Fig.\,\ref{fig:eval}, we demonstrate a concrete example of such
a type preserving evaluator for a very simple expression language (|Expr|).

Our type universe (|Ty|) for the expression language consists of numbers and
booleans, represented by the constants |I| and |B|. We want to evaluate an
expression to a value, which may be either numeric (|IV n|) or boolean (|BV b|).
Note that the value datatype (|Val|) is indexed by constant terms (|I| and |B|)
of the type universe (|Ty|).

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
of how term indices appearing in types are treated in Nax, in contrast to how
they are treated in Haskell and Agda.

\subsubsection{The kind syntax and well-sortedness:}
In all three languages, the datatype |Val| has the kind annotated |Ty -> *|,
which means that |Val| is a unary type constructor that expects a term of
type |Ty|, rather than a type (c.f., a unary type constructor that expects
a type has kind |* -> *|). Although the textual form (|Ty -> *|) of the kind
happens to coincide in these three languages, each language has its own
kind syntax and justifications for well-sortedness (\aka\ kind validity)
as illustrated in Table\;\ref{tbl:sorting}.

The datatype promotion extension ({\small\texttt{DataKind}}) for Haskell
works as follows:
(1) check if a type constructor |T| is well-kinded
    ($\Jty T : \overline{\star} -> \star$),
(2) promote |T| to the kind level
    (note $T\,\overline{\kappa}\,$ in the kind syntax), and
(3) check well-sortedness of the promoted |T| used in kinds
    ($\Jki T\,\overline{\kappa} : |BOX|$).
In our example, we need not worry about the arguments to the type constructor
since |Ty| is a just a type (\ie, nullary type constructor).
The justification for $\Jki |Ty -> * : BOX|$ is illustrated at
the left bottom corner in the Table\;\ref{tbl:sorting}.
Note the promotion of |Ty|, from $\Jty |Ty : *|$ to $\Jki |Ty : BOX|$.
The datatype promotion extension is closely related to, in fact, motivated
by the universe subtyping in Agda, which we will shortly explain.

\begin{table}
\hspace*{-3ex}
\begin{tabular}{ccc}
\textsc{Haskell} \textcolor{gray}{\texttt{+ DataKind}}
&
\textsc{Nax}
&
\textsc{Agda} 
\\
|* : BOX| &
|* : BOX| &
$\star_0 : \star_1 : \star_2 : \star_3 : \cdots$
\\ & &
$\stackrel{\parallel}{|*|}~\,\stackrel{\parallel}{|BOX|}~~\quad\qquad\qquad$
\\
|kappa ::= * || kappa -> kappa | $\mid$
  \textcolor{magenta}{$T\,$}$\overline{\kappa}$
&
|kappa ::= * || kappa -> kappa | $\mid$
   \textcolor{magenta}{$A\,$}|-> kappa|
&
\begin{minipage}{.37\linewidth}\small\centering
term/type/kind/sort syntax are\\ merged into one pseudo-term
\end{minipage}
\\ \\
{ \inference{ \inference{\Jty |Ty : *|}{\Jki |Ty : BOX|} & \Jki |* : BOX| }{
    \Jki |Ty -> * : BOX| }
} & ~~
{ \inference{ \Jty |Ty : *| & \Jki |* : BOX| }{ \Jki |Ty -> * : BOX| }
}
& \qquad
{ \inference{ \!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!
              \inference{||- |Ty : *| & |* <= BOX|}{||- |Ty : BOX|}
            & ||- |* : BOX| }{
    ||- |Ty -> * : BOX| }
}
\end{tabular} \vskip2ex
\caption{The universe structure, kind syntax, and justifications for
	well-sortedness of the kind |Ty -> *| in three different languages.}
\label{tbl:sorting}
\end{table}

Agda has stratified type universes. That is, there are countably many stars
$\star_0,\star_1,\dots$ such that $||- \star_n : \star_{1+n}$. When we
construct an arrow in Agda, that is, $||- |kappa1 -> kappa2| : \star_n$,
its well-formedness condition is when $||- |kappa1| : \star_n$ and
$||- |kappa2| : \star_n$. However, requiring |kappa1|, |kappa2|, and
|kappa1 -> kappa2| to be in exactly the same universe can cause a lot of
code duplication. For example, if we have $||- |Ty| : \star_0$ and
we want to construct $|Ty| -> \star_0$, we cannot do this since
$||- \star_0:\star_1$. To work around the universe difference, we
would need to duplicate another datatype $||- |Ty'| : \star_1$,
which is isomorphic to |Ty| but at one higher level. Only then,
we can construct $|Ty'| -> \star_0$. Then, if one needs
$|Ty| -> \star_1$, we would need yet another duplicate |Ty''|
at yet another higher level. Universe subtyping provides a remedy
to this duplication problem by allowing objects at lower universe
to be considered as objects as higher universe -- in other words,
it is `promoted' to upper level. This gives us a notion of subtyping
such that $\star_i \leq \star_j$ where $i \leq j$.\footnote{
	This is not the only rule for universe subtyping.
 	Another important rule is subtyping between arrows.
	See Ulf Norell's thesis TODO cite for details.}
With universe subtyping, we can construct arrows from |Ty| to any level of
universe (\eg, $|Ty| -> \star_0$, $|Ty| -> \star_1$, $\dots$). Relating back to
the datatype promotion in Haskell, $\star_0$ and $\star_1$ corresponds to |*|
and |BOX| in Haskell. So, we wrote |*| and |BOX| instead of $\star_0$ and
$\star_1$ in the justification of well-formedness of |Ty -> *| in Agda
(at right bottom corner in Table\;\ref{tbl:sorting}) to make the comparison
more apparent.

Nax, on the other hand, TODO



\subsubsection{Use of term indices in types:}
TODO



\subsection{Generic indexed lists parametrized by a binary relation}

\afterpage{
\begin{landscape}
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
\end{landscape}
} % end afterpage

22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here
22222 write text here 22222 write text here 22222 write text here





\subsection{Stack safe compiler for the expression language}

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

33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here
33333 write text here 33333 write text here 33333 write text here


