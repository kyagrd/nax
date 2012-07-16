%include includelhs2tex.lhs

%include mendler/CataViaHisto.lhs
%include mendler/Proof.lhs

\section{Properties of the recursion combinators}
\label{sec:proof}
We close this chapter by summarizing the termination properties of
the recursion combinators and the relation between the recursion combinators
we discussed so far.

TODO also discuss other possibilities families of recursion combinators
and difficulties of defining them, e.g., msfcv-

TODO table that summarizes the termination property
(extend from table at the end of ICFP paper)

\begin{figure}
\ProofCata
\caption{\normalsize $F_{\omega}$ encoding of |Mu0| and |mcata0| in Haskell}
\label{fig:proof}
\end{figure}

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

\begin{figure}
\CataViaHisto
\caption{\normalsize Alternative definition of iteration via course-of-values iteration.}
\label{fig:cataviahisto}
\end{figure}

Figure \ref{fig:cataviahisto} illustrates a well known fact that a standard
iteration (|mcata|) is a special case of a course-of-values iteration (|mhist|).
Note that |mcata| is defined in terms of |mhist|
by ignoring the inverse operation (|out|).

Similarly, We can define |mcata| in terms of |mprim|, and,
|mhist| in terms of |mcvpr|, by ignoring the casting operation of
the primitive recursion families. It is also quite evident that
we can define |mcata| in terms of |msfcata|.

TODO need come back and finish this section later on, since I
haven't really worked on embedding CV families into Fix calclui.
