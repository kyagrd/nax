%include includelhs2tex.lhs

%include mendler/CataViaHisto.lhs
%include mendler/Proof.lhs

\section{Properties of recursion combinators}
\label{sec:proof}
We close this chapter by summarizing the termination properties
of Mendler-style recursion combinators
(Table \ref{tbl:mendlerCombinatorSummary}) and the relationships
between those combinators (Figure \ref{fig:cataviahisto})
(\ie, which combinators can be defined in terms of others).

\begin{table}\centering
\begin{tabular}{llll}
       & positive & negative & example\\\hline
|cata| & {proof} \cite{hagino87phd} & {undefined} & |len| \S\ref{ssec:convCata} \\
|mcata0| & {proof Figure} \ref{fig:proof} &  {proof Figure} \ref{fig:proof} & |len| {Figure} \ref{fig:len}\\
|mhist0| & {proof} \cite{vene00phd} & {no} & |fib| {Figure} \ref{fig:fib} \\
|msfcata0| & {proof} \S\ref{App:Fomega} & {proof} \S\ref{App:Fomega} & {|showExp|} {Figure} \ref{fig:HOASshow} \\
|msfhist0| & {argument}~\S\ref{ssec:tourHist0} & {no} & |loopFoo| {Figure} \ref{fig:LoopHisto} \\
|mprim0| & proof \cite{AbeMat04} & proof \cite{AbeMat04} & |factorial| Figure \ref{fig:fac} \\
|mcvpr0| & conjecture \S\ref{sec:fixi:cv} & no &  |lucas| Figure \ref{fig:lucas} \\
|mcata1| & {proof} \cite{AbeMatUus05} & {proof} \cite{AbeMatUus05} & |bsum| {Figure} \ref{fig:bsum} \\
         & & & |extev| {Figure} \ref{fig:mutrec} \\
|mhist1| & {similar} to |mcvpr1| & {no} & |switch2| {Figure} \ref{fig:vec} \\
|msfcata1| & {similar} to |msfcata0| & {similar} to |msfcata0| & \\
|msfhist1| & {similar} to |msfhist0| &  {no} &  
\end{tabular}
\caption{Termination properties of Mendler-style recursion combinators.}
\label{tbl:mendlerCombinatorSummary}
\end{table}

\begin{figure}
\ProofCata
\caption{\normalsize $F_{\omega}$ encoding of |Mu0| and |mcata0| in Haskell.}
\label{fig:proof}
\end{figure}

\index{termination!Mendler-style iteration}
We give a termination proof for the Mendler-style iteration
(at kind $*$) in Figure~\ref{fig:proof}. The proof takes the form
of an embedding into \Fw, which is known to be strongly normalizing.
The proof in Figure~\ref{fig:proof} is adapted from work by \citet{AbeMatUus05}.
They prove termination of the Mendler-style iteration at arbitrary kinds.
A proof similar to Figure~\ref{fig:proof} is also given by \citet{vene00phd}.

The definitions given in Figure \ref{fig:proof} are $F_\omega$ terms,
but are also legal Haskell terms that execute in GHC. Try the following code
with the definitions of |Mu0| and |mcata0| from Figure \ref{fig:proof}.
They run and return the expected results!\vspace*{-3ex} \label{pageNatFw}
\begin{center}
\ProofCataEx
\end{center}\vskip1ex

\index{termination!Mendler-style primitive recursion}
\citet{AbeMat04} proved termination of Mendler-style primitive recursion
(|mprim|) by a reduction preserving embedding of |mprim| into \Fixw.
We discuss the details of this embedding in \S\ref{sec:fixi:data}.
We know that the Mendler-style course-of-values recursion (|mcvpr|)
does not terminate for negative datatypes since |mhist| does not terminate
for negative datatypes. Any computation that can be defined by |mcata|
can also be defined by |mcvpr| (where it may be more efficient).
We show a partial proof that |mcvpr0| terminates for regular positive datatypes
in \S\ref{sec:fixi:cv}, and we conjecture that |mcvpr|
terminates for positive datatypes at higher-kinds as well.

\citet{vene00phd} stated that we can deduce the termination of
the Mendler-style course-of-values iteration for positive datatypes from its
relation to the conventional course-of-values iteration, but he did not clearly
discuss whether the termination property holds for negative datatypes.
In our work, we demonstrated that |mhist0| may not terminate
for negative datatypes by exhibiting the counterexample
(Figure \ref{fig:LoopHisto}) in \S\ref{ssec:tourNegative}.

Figure \ref{fig:cataviahisto} illustrates a well-known fact that a standard
iteration (|mcata|) is a special case of a course-of-values iteration (|mhist|).
Note that |mcata| is defined in terms of |mhist|
by ignoring the inverse operation (|out|).
Similarly, we can define |mcata| in terms of |mprim| and
|mhist| in terms of |mcvpr| by ignoring the casting operation of
the primitive recursion families.

%% It is also quite evident that we can define |mcata| in terms of |msfcata|.

\begin{figure}[b]
\CataViaHisto
\caption{\normalsize Alternative definition of iteration via the course-of-values iteration.}
\label{fig:cataviahisto}
\end{figure}



