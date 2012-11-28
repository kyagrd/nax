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

In Figure\;\ref{fig:compile}, we implement a stack-safe
compiler for the same expression language (|Expr| in Fig.\;\ref{fig:eval})
discussed in Sect.\;\ref{ssec:eval}. In Fig.\;\ref{fig:eval} of that section 
we implemented an index preserving evaluator
|eval : Expr {t} -> Val {t}|. Here,
the stack-safe compiler |compile : Expr {t} -> Code {ts} {`cons t ts}|
uses the index to enforce stack safety
-- an expression of type |t| compiles to some code, which when run on
a stack machine with an initial stack configuration |ts|, terminates 
with the final stack configuration |cons t ts|.

A stack configuration is an abstraction of the stack 
that tracks only the types of the values stored there.
We represent a stack configuration as
a list of type representations (|List Ty|).\footnote{
	The astute reader may wonder why we use |List| instead of the
	already defined |List'| in Fig.\;\ref{fig:glist}, which is exactly
	the plain list we want. In Nax and Agda, it is possible to have
	term indices of |List' Ty| instead of |List Ty|. (In Nax and Agda,
	the |List| datatype is defined in their standard libraries.)
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
 

