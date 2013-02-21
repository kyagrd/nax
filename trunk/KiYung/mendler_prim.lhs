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
          at kinds $*$ and $* -> *$, in comparison with |mcata| and |mhist|.}
\label{fig:mprim}
\end{figure}
\end{landscape}

\section{Mendler-style primitive recursion (|mprim|)} \label{sec:mpr}

In Figure \ref{fig:mprim} we list a type declaration and a 
defining equation for a several families of Mendler-style recursion combinators.
We give two versions for each family, one at kind $*$ and one at kind $* -> *$.
The families of combinators increase in complexity from iteration (|mcata|),
through primitive recursion (|mprim|) and course-of-values iteration (|mhist|),
to course of values primitive recursion (|mcvpr|).
We saw |mcata| and |mhist| in the previous sections.

The Mendler-style primitive recursion family (|mprim|), when
compared to the |mcata| family, has an additional
abstract operation, which we call |cast|.
The |cast| operation explicitly converts a value of the abstract recursive type
(|r|) into a value of the concrete recursive type (|Mu0 t|). 

Similarly,
the Mendler-style course-of-values primitive recursion family (|mcvpr|),
when compared to the |mhist| family, also has
an additional |cast| operation.

Since |mprim| has an additional abstract operation, when compared to |mcata|,
it can express all the functions expressible with |mcata|. In some programs,
the additional |cast| operation, can increase the efficiency of the program
by supporting constant time access to the concrete value of the
recursive component.


A typical example of primitive recursion is the factorial function.
Figure \ref{fig:fac} illustrates the general recursive version (right) and
the Mendler-style version (left) of the factorial function, where
|times :: Nat -> Nat -> Nat| is the usual multiplication operation on
natural numbers. Note, the definition of |phi| in the Mendler-style is
similar to the definition of |fac| in the general recursive version,
except that it uses the explicit |cast| to convert from an abstract value
(|n:r|) to a concrete value (|cast n : Nat|).

\begin{figure}
$\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!$
\begin{minipage}{.5\linewidth}\small \ExFacG \end{minipage}
\begin{minipage}{.6\linewidth}\small \ExFac \end{minipage}
\caption{|mprim0| example: factorial function}
\label{fig:fac}
\end{figure}

The primitive recursion family also enables programmers to define non-recursive functions,
such as a constant time predecessor for natural numbers
(Figure \ref{fig:constpred}) and a constant time tail function for lists
(Figure \ref{fig:consttail}).
Although it is possible to implement |factorial|, |pred|, and |tail|
in terms of |mcata|, those implementations will be less efficient.
The time complexity of |factorial| in terms of iteration
will be quadratic in the size of the input rather than being linear.
The time complexity of |pred| and |tail| in terms of iteration
will be linear in the size of the input rather than being constant.

\begin{figure}[p]
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
the |out| operation to the |mprim| family, as is shown in Figure \ref{fig:mprim},
just as the |mhist| family can be defined by adding the |out| operation
to |mcata|. The |mcvpr| family is only guaranteed to terminate for
positive datatypes, for the same reason that the |mhist| family is
only guaranteed to terminate for positive datatypes (recall Figure \ref{fig:LoopHisto}).

A simple variation of the Fibonacci function, shown  in Figure \ref{fig:lucas},
is an example of a course-of-values primitive recursion.
The Fibonacci function |fib| and the Lucas function |luc| satisfy
the following recurrence relations:\footnote{
The |luc| function in Figure \ref{fig:lucas} is slightly
different from the original version of Lucas numbers.
What |luc n| implements is the function $Lucas(n+1) - (n+1)$, 
where $Lucas$ is the original
definition of the Lucas number. Mathematically, Lucas numbers are just a
Fibonacci sequence with different base values. They can be understood
as a Fibonacci number offset by linear term. For instance, |luc| can be turned
into a Fibonacci function via change of variable by |fib n = luc n + n + 1|.}
\begin{code}
fib (n+2)  = fib (n+1)  + fib n
luc (n+2)  = luc (n+1)  + luc n + n
\end{code}
Note the trailing ``$\cdots+\,$|n|'' in the recurrence relation for |luc|.
We need the ability of course-of-values recursion because $n$ is
a deep recursive component of $n+2$ (\ie, $n$ is the predecessor of
the predecessor of $n+2$). We need primitive recursion, since we not only perform
a recursive call over $n$ ($\cdots+\,$|luc n|$\,+\cdots$), but also add the value
of $n$ itself ($\cdots+\,$|n|). The |mcvpr| family provides
both |out| and |cast| operations for accessing deep recursive components and
casting from an abstract value to a concrete recursive value.

\begin{figure}
\begin{minipage}{.5\linewidth}\small \ExLucasG \end{minipage}
\begin{minipage}{.5\linewidth}\small \ExLucas \end{minipage}
\caption{Lucas number {\small (\url{http://oeis.org/A066982})} example
         illustrating the use of the |mcvpr0| family.}
\label{fig:lucas}
\end{figure}

It is strongly believed that the primitive recursion family cannot be
embedded in \Fw\ in a reduction preserving manner, since it is known that
induction is not derivable from second-order dependent calculi \cite{Geuvers01}.
As we mentioned in \S\ref{mendler_history}, the termination properties of
Mendler-style primitive recursion can be shown by embedding |mprim| into
\Fixw\ \cite{AbeMat04} (also described in Section \ref{sec:fixi:data}.
Additionally, we discovered how to embed |mcvpr| within \Fixw.
However, our embedding of |mcvpr| into \Fixw\ (or, \Fixi) is not
reduction preserving. We will explain the details of the embedding
of |mprim| into \Fixw\ in Section \ref{sec:fixi:cv}.

