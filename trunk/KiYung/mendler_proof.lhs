%include includelhs2tex.lhs

\section{Properties of the recursion combinators}
\label{sec:proof}

We briefly discuss the termination properties of the recursion combinators
and the relation between the recursion combinators we discussed so far

We illustrate the termination proof for the Mendler-style iteration
for kind $*$ in Figure \ref{fig:proof}.  This embedding of |Mu0| and |mcata0|
into $F_\omega$ is a proof of termination provided that $F_\omega$ extended
with non-recursive datatypes is normalizing. These definitions actually run
in GHC. Try the following code with the definitions of |Mu0| and |mcata0|
in Figure \ref{fig:proof}. It will run!
\begin{center}
\ProofCataEx
\end{center}
We translated the proof in Figure \ref{fig:proof} from the work by
\citet{AbeMatUus05}, which discuss more generally on arbitrary ranks.
A proof similar to Figure \ref{fig:proof} is also given by \citet{vene00phd}.

\citet{vene00phd} also give discussions that we can deduce the termination of
the Mendler-style course-of-values iteration for positive datatypes from its
relation to conventional course-of-values iteration, but he does not clearly
discuss whether the termination property holds for negative datatypes.
In our work, we disproved the termination of |mhist0| for negative datatypes
by showing the counter-example (Figure \ref{fig:LoopHisto})
in \S\ref{ssec:tourNegative}.

Figure \ref{fig:cataviahisto} illustrates a well known fact that a standard
iteration (|mcata|) is a special case of a course-of-values iteration (|mhist|).

Although we do not have a formal argument, it seems quite evident that
we can simulate all the standard combinators (e.g., |mcata0|) via
its inverse augmented counterparts (e.g., |msfcata0|). That is, all functions
definable using |mcata0| are definable using |msfcata0| instead.

