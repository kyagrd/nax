%include includelhs2tex.lhs
\section{$F_\omega$ encoding of |Rec0| and |msfcata0|}\label{App:Fomega}

%include mendler/Proof2.lhs


\begin{figure}
\ProofSFCata
\SumDef
\caption{$F_\omega$ encoding of |Rec0|, |msfcata0|, and the sum type (+).}
\label{fig:proofsf}
\end{figure}
 
%% \begin{figure}
%% \SumDef
%% \caption{$F_\omega$ encoding of the sum type}
%% \label{fig:sumdef}
%% \end{figure}

\begin{figure}
\HOASshowFw
\caption{HOAS string formatting example in $F_\omega$.}
\label{fig:HOASshowFw}
\end{figure}

Figure \ref{fig:proofsf} is the $F_\omega$ encoding of the inverse augmented datatype
|Rec0| and its catamorphism |msfcata0|.  We use the sum type to encode |Rec0|
since it consists of two constructors, one for the inverse and the other for
the recursion.  The newtype |Id| wraps answer values inside the inverse.  
The catamorphism combinator |msfcata0| unwraps
the result (|unIn|) when |x| is an inverse.  Otherwise, |msfcata0| runs the
combining function |phi| over the recursive structure |(\f->f(phi Id))|.
The utility function |lift| abstracts a common pattern, useful
when we define the shorthand constructors (|lam| and |app|).

Figure \ref{fig:proofsf} also contains the $F_\omega$ encoding of the sum type
|(+)| and its constructors (or injection functions) |inL| and |inR|.
The case expression |caseSum| for the sum type is just binary function
application. In the $F_\omega$ encoding, they could be omitted
(i.e., |caseSum x f g| simplifies to |x f g|).  But, we choose to write
in terms of |caseSum| to make the definitions easier to read.

In Figure \ref{fig:HOASshowFw}, we define both an inductive datatype for HOAS (|Exp|), and the string formatting function
(|showExp|), 
with these $F_\omega$ encodings, just as we did in \S\ref{ssec:showHOASmsfcata}.
We can define simple expressions using the shorthand constructors and print out
those expressions using |showExp|.  For example, \\
\begin{quote}\noindent
$>$ |putStrLn (showExp (lam(\x->lam(\y->x))))|\\
\verb|(\a->(\b->a))|
\end{quote}


\section{Properties of the recursion combinators}
\label{sec:proof}

We briefly discuss the termination properties of the recursion combinators
and the relation between the recursion combinators.

We illustrate the termination proof for Mendler style catamorphism for rank 0
in Figure \ref{fig:proof}.  This embedding of |Mu0| and |mcata0| into
$F_\omega$ is a proof of termination provided that $F_\omega$ extended with
non-recursive datatypes is normalizing.
These definitions actually runs in GHC.\footnote{with a deprecated extension
\texttt{ImpredicativeTypes}} Try the following code with the definitions of
|Mu0| and |mcata0| in Figure \ref{fig:proof}. It will run!\vspace*{-.5em}
\begin{center}
\ProofCataEx
\end{center}
We translated the proof in Figure \ref{fig:proof} from the work by
\citet{AbeMatUus05}, which discuss more generally on arbitrary ranks.
A proof similar to Figure \ref{fig:proof} is also given by \citet{vene00phd}.

\citet{vene00phd} also give discussions that we can deduce the termination
of Mendler style histomorphism for positive datatypes from its relation to
conventional histomorphism, but he does not clearly discuss whether
the termination property holds for negative datatypes.  In our work,
we disproved the termination of |mhist0| for negative datatypes by showing
the counter-example (Figure \ref{fig:LoopHisto}) in \S\ref{ssec:tourNegative}.

Figure \ref{fig:cataviahisto} illustrates a well known fact that catamorphism
is a special case of histomorphism.

Although we do not have a formal argument, it seems quite evident that
we can simulate all the standard combinators (e.g., |mcata0|) via
its inverse augmented counterparts (e.g., |msfcata0|).

