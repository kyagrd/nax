%include includelhs2tex.lhs
%include mendler/FacG.lhs
%include mendler/Fac.lhs

\begin{landscape}
\begin{figure}
$\!\!\!\!\!\!\!\!\!$\mprimDef
\caption[The Mendler-style primitive recursion and
         course-of-values primitive recursion]
         {The Mendler-style primitive recursion (|mprim|) and
          the Mendler-style course-of-values primitive recursion (|mcvpr|)
          for kinds $*$ and $* -> *$, in comparison with |mcata| and |mhist|.}
\label{fig:mprim}
\end{figure}
\end{landscape}

\section{Mendler-style primitive recursion} \label{sec:mpr}
The Mendler-style primitive recursion family (|mprim|) has an additional
abstract operation, which we call |cast|, compared to the |mcata| family.
The |cast| operation explicitly converts a value of the abstract recursive type
(|r|) into a value of the concrete recursive type (|Mu0 t|). Similarly,
the Mendler-style course-of-values primitive recursion family (|mcvpr|) has
an additional |cast| operation, compared to the |mhist| family.
The type signatures and the definitions of |mprim| and |mcvpr| for kinds
$*$ and $* -> *$ are given in Figure \ref{fig:mprim}, along with
the type signatures and the definitions of the Mendler-style iteration
family (|mcata|) the Mendler-style course-of-values iteration family (|mhist|)
for comparison.

Since |mprim| has an additional abstract operation when compared to |mcata|,
it can express all the functions expressible with |mcata|, but often more
efficiently because of the additional |cast| operation.

A typical example of primitive recursion is the factorial function.
Figure \ref{fig:fac} illustrates the general recursive version (right) and
the Mendler-style version (left) of the factorial function, where
|times :: Nat -> Nat -> Nat| is the usual multiplication operation on
natural numbers. Note, the definition of |phi| in the Mendler-style is
similar to the definition of |fac| in the general recursive version,
except that it uses explicit |cast| to convert from an abstract value
(|n:r|) to a concrete value (|cast n : Nat|).

\begin{figure}
$\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!$
\begin{minipage}{.5\linewidth}\small \ExFacG \end{minipage}
\begin{minipage}{.6\linewidth}\small \ExFac \end{minipage}
\caption{|mprim0| example: factorial function}
\label{fig:fac}
\end{figure}

The primitive recursion also enables us to define non-recursive functions,
such as a constant time predecessor for natural numbers
(Figure \ref{fig:constpred}) and a constant time tail function for lists
(Figure \ref{fig:consttail}).
Although it is possible to implement |factorial|, |pred|, and |tail|
in terms of |mcata|, those implementations will be less efficient.
The time complexity of |factorial| in terms of iteration
will be quadratic to the input rather than being linear to the input.
The time complexity of |pred| and |tail| in terms of iteration
will be linear to the input rather than being constant.

\begin{figure}
\begin{minipage}{.5\linewidth}\small \ExPredG \end{minipage}
\begin{minipage}{.6\linewidth}\small \ExConstPred \end{minipage}
\caption{|mprim0| example (non-recursive): a constant time predecessor}
\label{fig:constpred}
\end{figure}

\begin{figure}
\begin{minipage}{.5\linewidth}\small \ExTailG \end{minipage}
\begin{minipage}{.6\linewidth}\small \ExConstTail \end{minipage}
\caption{|mprim0| example (non-recursive):
         a constatn time tail function for lists}
\label{fig:consttail}
\end{figure}

The course-of-values primitive recursion family can be defined by adding
the |out| operation to the |mprim| family, as in Figure \ref{fig:mprim},
just as the |mhist| family can be defined by adding the |out| operation
to |mcata|. The |mcvpr| family is only guaranteed to terminate for
positive datatypes for the same reason that the |mhist| family is
only guaranteed to terminate for positive datatypes.

A simple variation of a Fibonacci function in Figure \ref{fig:lucas}
is an example of a courses-of-values primitive recursion.
The Fibonacci function |fib| and the Lucas function |luc| satisfy
the following recurrence relations:\footnote{
In fact, the original definition of Lucas number is different from this.
What |luc| implements is $Lucas(n+1) - (n+1)$, where $Lucas$ is the original
definition of the Lucas number. Mathmatically, Lucas numbers are just
Fibonacci sequence with different base values so that they can be understood
as a Fibonacci numbers offset by linear term. For instance, |luc| can be tunred
into a Fibonacci function via change of variable by |fib n = luc n + n + 1|.}
\begin{code}
fib (n+2)  = fib (n+1)  + fib n
luc (n+2)  = luc (n+1)  + luc n + n
\end{code}
Note the traliing ``$\cdots+\,$|n|'' in the recurrens relation for |luc|.
We need the ability of course-of-values recursion since $n$ is
a deep recursive component of $n+2$ (\ie, $n$ is a predecessor of
a precessor of $n+2$). We need primitive recursion since we not only perform
a recurse call over $n$ ($\cdots+\,$|luc n|$\,+\cdots$) but also use the value
of $n$ itself for addition ($\cdots+\,$|n|). The |mcvpr| family provides
both |out| and |cast| operations for deep recursive calls and casting
from an abstract value to a concrete recursive vaule.

\begin{figure}
$\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!$
\begin{minipage}{.6\linewidth}\small \ExLucasG \end{minipage}
\begin{minipage}{.6\linewidth}\small \ExLucas \end{minipage}
\caption{|mcvpr0| example: Lucas number (\url{http://oeis.org/A066982})}
\label{fig:lucas}
\end{figure}

