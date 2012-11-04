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

In Figure\;\ref{fig:compile}, we provide implementations of a stack safe
compiler for the same expression language (|Expr| in Fig.\;\ref{fig:eval}),
which we discussed in Sect.\;\ref{ssec:eval}. The type preserving evaluator
|eval : Expr {t} -> Val {t}| in Fig.\;\ref{fig:eval} was a index preserving
program where the index of the input type (|Expr|) and
the result type (|Val|) are exactly the same (|t|).
The stack safe compiler |compile : Expr {t} -> Code {ts} {`cons t ts}|
uses the type index to enforce a more interesting property of stack safety
-- an expression of type |t| compiles to a code, which are to run on
a stack machine with an initial stack configuration |ts| and end up
in the finial stack configuration |cons t ts| after running the code.
In other words, running the compiled code of |Expr {t}| on a stack machine
should put a |Val {t}| on top of the stack it started with.

The stack configuration is an abstraction of the stack, which only keeps track
of the types of the stack values. We represent a stack configuration as
a plain regular list of type representations (|Ty|). For instance,
the configuration for the stack containing three values (from top)
3, True, and 4 (to bottom) is (cons I (cons B (cons I Nil))).
We represent the stack configuration as a plain list of type representations
(|List Ty|).

Astute reader may wonder why we define |List| again instead of using
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

To enforce the stack safety, we index each instruction
(|Inst : List Ty -> List Ty -> *|) with its initial and
final stack configuration, and then define the |Code| as a |Path|
following the transition relation defined by each of the instruction step
(\ie, |Code {ts} {ts'}| is a synonym of |Path Inst {ts} {ts'}|).
For example, the compiled code consisting of three instruction sequences
|inst1 : Inst {ts0} {ts1}|,
|inst2 : Inst {ts1} {ts2}|, and
|inst3 : Inst {ts2} {ts3}| has the type |Code {ts0} {ts3}|.
Review the |Path| datatype (Fig.\;\ref{fig:glist}) 
discussed in Sect.\ref{ssec:glist} for details.

Note that each instruction (|Inst {ts} {ts'}|) is indexed by
its expected initial stack configuration |ts| and
its final stack configurations |ts'|, which is the stack configuration
after running the instruction from the initial configuration.
For example, |pLUS : Inst {`cons I (`cons I ts)} {`cons I ts}|
instruction expects two numeric values on top of the stack
in order to perform numeric addition. Running the |pLUS| instruction
will consume those two numeric values on the top and put a new numeric value,
which is the result of the addition, on top of the stack, remaining the rest of
the stack unchanged.

