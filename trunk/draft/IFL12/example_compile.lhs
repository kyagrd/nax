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

In Figure\;\ref{fig:compile}, we implement a stack safe
compiler for the same expression language (|Expr| in Fig.\;\ref{fig:eval})
discussed in Sect.\;\ref{ssec:eval}. In Figure \ref{fig:eval} of that section 
we implemented an index preserving evaluator
|eval : Expr {t} -> Val {t}|. Here,
the stack safe compiler |compile : Expr {t} -> Code {ts} {`cons t ts}|
uses the index to enforce stack safety
-- an expression of type |t| compiles to some code, which when run on
a stack machine with an initial stack configuration |ts|, terminates 
with the final stack configuration |cons t ts|.
A stack configuration is an abstraction of the stack 
that tracks only the types of the values stored there.


We represent a stack configuration as
a list of type representations (|List Ty|). For instance,
the configuration for the stack containing three values (from top to bottom)
[3, True, 4] is |cons I (cons B (cons I Nil))|.


DOES NOT BELONG HERE
The astute reader may wonder why we define |List| again instead of using
already defined |List'| in Fig.\;\ref{fig:glist}, which is exactly
the plain regular list specialized from generic |Path|.
It is possible to represent stack configuration as |List' Ty| in Nax and Agda,
but unfortunately not in Haskell. Haskell's datatype promotion does not allow
promoting datatypes indexed by already promoted datatypes. So, in Haskell,
we cannot index types by |List' Ty|, which is a synonym of
|Path (Elem Ty) () ()| indexed by a promoted Haskell unit term |()|
of the promoted Haskell unit type |()|.
In Sect. \label{sec:discuss}, we will discuss further on how the two approaches
of Nax verses Haskell differ in their treatment of term indexed types.

To enforce stack safety, each instruction 
(|Inst : List Ty -> List Ty -> *|) is indexed with its initial and
final stack configuration. For example, |pLUS : Inst {`cons I (`cons I ts)} {`cons I ts}|
instruction expects two numeric values on top of the stack. 
Running the |pLUS| instruction
will consume those two values, replacing them with a new numeric value
(the result of the addition) on top of the stack, leaving the
rest of the stack unchanged.

We define |Code| as a |Path|
of stack consistent instructions
(\ie, |Code {ts} {ts'}| is a synonym for |Path Inst {ts} {ts'}|
from Sect. \ref{ssec:glist}).
For example, the compiled code consisting of the three instructions
|inst1 : Inst {ts0} {ts1}|,
|inst2 : Inst {ts1} {ts2}|, and
|inst3 : Inst {ts2} {ts3}| has the type |Code {ts0} {ts3}|.
 


