%include includelhs2tex.lhs
\section{Mendler-style course-of-values iteration for regular datatypes}
\label{ssec:tourHist0}
Some computations are not easily expressible by iteration,
since iteration only recurses on the direct subcomponents (e.g., tail
of a list). Terminating recursion shcemes on deeper subcomponents
(e.g., tail of tail of a list) requires rather complex encodings
in the conventional setting. Unfortunately, functional programmers often
write simple recursive functions using nested pattern matching that
recurse on deep subcomponents exposed by the nested patterns.
A typical example is the Fibonacci function:
\vspace*{.5em}
\begin{code}
fib Z          = 0
fib (S Z)      = 1
fib (S (S m))  = fib (S m) + fib m
\end{code}\vspace*{-.5em}\\
Note, in the third equation |fib| recurses on both the predecessor |(S m)|,
which is a direct subcomponent of the argument, and the predecessor of
the predecessor |m|, which is a deeper subcomponent of the argument.
The Histomorphism \cite{UusVen99histo} captures such patterns of recursion.
The Histomorphism is also known as the course-of-values iteration.

In the conventional style, course-of-values iteration are defined through
co-algebraic construction of an intermediate stream data structure that
pairs up the current argument and the results from the previous steps.
There are two ways of implementing this.  One is a memoizing bottom-up version,
and the other is a non-memoizing version that repeats the computation of
the previous steps.  We are not going to show or discuss those implementations
here, but the point we want to make is that both versions need to be
implemented through co-algebraic construction \cite{UusVen00,vene00phd}.
Course-of-values iteration expressed in terms of this co-algebraic style will
look very different from its equivalent in general recursion style. One needs
to extract both the original arguments and the deep result values from the
stream explicitly calling on stream-head and stream-tail operations.
However, in the Mendler style, we do not need such co-algebraic construction
at least for the non-memoizing version.\footnote{The Mendler-style
histormophism combinators implemented here are the non-memoizing ones.
\citet{vene00phd} suggests how to implement a memoizing 
Mendler-style histomorphism, which uses co-algebraic construction.}.

In the Mendler-style course-of-values iteration (|mhist|),
we play the same trick we played in the Mendler-style iteration (|mit|).
We arrange for the combining function to take additional arguments
(Figures \ref{fig:rcombty} and \ref{fig:rcombdef}).
\begin{itemize}
  \item The combining function |phi| now becomes a function of 3 arguments. 
        The first argument is a function that represents an
        abstract unrolling function that projects out the value
        embedded inside the data constructor |In0| by accessing
        the projection function |out0| given in the definition.
        As in |mcata0|,
        the next argument represents a recursive placeholder, and
        the last argument represents the base structure
        that must be combined into an answer.

  |mhist0 phi (In0 x) = phi out0 (mhist0 phi) x|

  \item Again we use higher-rank polymorphism to insist that 
        the abstract unrolling function, with type (|r -> f r|),
        the recursive placeholder function, with type (|r -> a|), and
%%%%%%% the recursion points, with type (|r|), in
        the base structure, with type (|f r|), only work
        over an abstract type, denoted by (|r|).
        
  |mhist0 :: (forall r . (a -> f a) -> (r -> a) -> (f r -> a)) -> {-"\cdots"-}|
\end{itemize}  

The Mendler-style course-of-values iteration is much handier
than the conventional course-of-values iteration \cite{UusVen00}. For example,
in Figure \ref{fig:fib}, the definition for the Fibonacci function in the
general recursion style (left) and the definition in the Mendler style (right)
look almost identical.  Particularly, when we have unrolled the nested pattern
matching in the general recursive definition into a case expression.
The only difference between the two, is that in the Mendler style (left),
we pattern match over |out n| in the case expression, in the gerneral recursion
style (right) we pattern match over |n|.  

\begin{figure}
\begin{minipage}{.49\linewidth}
%include mendler/FibG.lhs
\end{minipage}
\begin{minipage}{.49\linewidth}
%include mendler/Fib.lhs
\end{minipage}
\caption{|mhist0| example: Fibonacci function}
\label{fig:fib}
\end{figure}

Let us visually relate the definition of |mhist0| with the second equation of
|phi| in the definition of the Fibonocci function as follows:
\begin{code}
mhist0 phi (In0 x) =  phi  out0            (mhist0 phi)         {-"~~"-}x
                           {-"~~\vdots"-}  {-"~~~~~\vdots"-}    {-"~~~\vdots"-}
                      phi  out             {-"~~~"-}fib         (S n)  =
                          case out n of
                            Z     -> 1
                            S n'  -> fib n + fib n'
\end{code}      
The abstract unrolling function |out| and the recursive placeholder |fib|
stand for the actual arguments |out0| and |(mhist0 phi)|, but the higher-rank
type of the combining function |phi| ensures that they are only used in a safe
manner.  The abstract unrolling function |out| enables us to discharge |In0|
as many times as we want inside |phi|. 

From the programmers perspective, |out0| is a hidden primitive,
hidden by the |mhist0| abstraction (\ie, only used within the definition of
combinators like |mhist0| but not in the user-defined functions).
But, inside the definition of the combining function |phi|,
the programmer can actually access the functionality of |out0|
through the abstract unrolling function |out|. The higher-rank types limit
the use of this abstract unrolling function |out| to values of type |r|.

In a positive recursive datatype, the only functions with domain |r|
are the abstract unroller, and the recursive placeholder.
The programmer can only
{\em whittle down} the |r| values inside the base structure,
of type (|f r|), into smaller structures, of type (|f r|). The programmer can
then decompose these into even smaller |r| values by pattern matching against
the data constructors of the base |f|. However, there is no way to combine
any of these decomposed |r| values to build up larger |r| values.
The only possible use of the decomposed |r| values is to call
the recursive placeholder, with type (|r -> a|).

For example,
in Figure \ref{fig:fib}, we pattern match over (|out n|),
discharging the hidden |In0| constructor of |n|.
Note the types inside the |(S n')| pattern matching branch: |n :: r|; |(out n) :: (N r)|; and |n' :: r|.
What can we possibly do with |n| and |n'|, of type |r|?  The only
possible computation is to call
 |fib :: r -> Int| on |n| and |n'|,  as we do in |fib n + fib n'|.
It is a type error to call |fib :: r -> Int| on either |(S n) :: N r|
or |(S n') :: N r|. This is why the termination property of |mhist0| continues to hold for
positive datatypes.

For negative datatypes, however, we have additional functions with domain |r|.
Inside the |phi| function passed to |mhist0|, the embedded functions with
negative occurrences, will have type |r| as their domain.
These can be problematic.  The counter-example to termination of |mhist0|
is in Figure \ref{fig:LoopHisto}, which will discussed in more detail
in \S\ref{ssec:tourNegative}.

