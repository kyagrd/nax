%include includelhs2tex.lhs

\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes #-}

import Prelude hiding (take, succ)

data Mu0 f = In0 { unIn0 :: f(Mu0 f) } -- use of |UnIn0| is restricted

data N r = Zero | Succ r
type Nat = Mu0 N
zero    = In0 Zero
succ n  = In0 (Succ n)

data L a r = Nil | Cons a r
type List a = Mu0 (L a)
nil        = In0 Nil
cons x xs  = In0 (Cons x xs)
\end{code}
\end{comment}

\section{Mendler-style recursion schemes over multiple values} \label{sec:relwork:mult}
There are many Mendler-style recursion schemes in addition
to those discussed in Chapter~\ref{ch:mendler}.
Here, we introduce two Mendler-style recursion schemes that
work over two (or more) structures simultaneously. 

\subsection{Simultaneous iteration}
\citet{UusVen00} studied course-of-value iteration (\aka\ histomorphism)
and \emph{simultaneous iteration} (\aka\ multimorhpism). They formulate
these two recursion schemes in both the conventional and Mendler style.
They show that the formulations are equivalent provided that the base structures
for recursive types are functors (\ie, positive). We have already discussed
Mendler-style course-of-values iteration in previous chapters.
Here, we introduce Mendler-style simultaneous iteration over
multiple recursive values, using the examples adopted from \citet{UusVen00}.
For simplicity, we only consider simultaneous iteration
over two recursive values, which can be transcribed into Haskell as follows:
%format msimit = "\textbf{msimit}"
%format msimpr = "\textbf{msimpr}"
%format msimit0 = msimit"_{*,*}"
%format msimpr0 = msimpr"_{*,*}"
%format r1
%format r2
%format f1
%format f2
%format x1
%format x2
\begin{singlespace}
\begin{code}
msimit0 :: (forall r1 r2. (r1 -> r2 -> a) -> f1 r1 -> f2 r2 -> a) -> Mu0 f1 -> Mu0 f2 -> a
msimit0 phi (In0 x1) (In0 x2) = phi (msimit0 phi) x1 x2
\end{code}
\end{singlespace}
\noindent
This recursion scheme simplifies function definitions
that simultaneously iterate over two recursive arguments.
For example, we can define |lessthan :: Nat -> Nat -> Nat|
and |take :: Nat -> List a -> List a| as follows:
\begin{singlespace}
\begin{code}
lessthan :: Nat -> Nat -> Bool
lessthan = msimit0 phi where
  phi lt Zero      Zero      = False
  phi lt Zero      (Succ _)  = True
  phi lt (Succ _)  Zero      = False
  phi lt (Succ m)  (Succ n)  = lt m n
{-""-}
take :: Nat -> List a -> List a
take = msimit0 phi where
  phi tk Zero      _            = nil
  phi tk (Succ _)  Nil          = nil
  phi tk (Succ n)  (Cons x xs)  = cons x (tk n xs)
\end{code}
\end{singlespace}\noindent
Note that the |phi| functions above are similar in structure to how one would typically
define |lessthan| and |take| using general recursion in Haskell. Although
it is possible to define these functions by multiple nested uses of |mit0|,
it is certainly not as simple as the definitions above (try it for yourself!).

The termination behavior of simultaneous iteration (|msimit|)
has not been studied when negative datatypes are involved.
Neither do we know of any studies that have embeded |msimit| into
a strongly normalizing typed lambda calculus.
For both course-of-values iteration (\McvIt) and recursion (\McvPr),
we have found conterexamples that nontermination is possible
for negative datatypes. The example that \McvIt\ does not always terminate
for negative datatypes can be found in Figure~\ref{fig:LoopHisto} in \S\ref{ssec:tourHist0},
p\pageref{fig:LoopHisto}. We also showed that \McvPr\ can be embedded
into \Fixi\ (or \Fixw) assuming monotonicity (\S\ref{sec:fixi:cv}).

One can imagine simultaneous recursion (|msimpr0|),
which has additional casting operations, as follows:
\begin{singlespace}
\begin{code}
msimpr0 :: (forall r1 r2  .   (r1 -> r2 -> a)      -- recursive call
                          ->  (r1 -> Mu0 f1)       -- cast1
                          ->  (r2 -> Mu0 f2)       -- cast2
                          ->  f1 r1 -> f2 r2 -> a) -> Mu0 f1 -> Mu0 f2 -> a

msimpr0 phi (In0 x1) (In0 x2) = phi (msimpr0 phi) id id x1 x2
\end{code}
\end{singlespace}\noindent
Extending primitive recursion (|mprim0|), which as has only one casting operation,
multiple casting operations are needed. One for 
each of the recursive arguments.
Here, we formulated |msimpr0| with two recursive arguments, so we have two
casting operations, whose types are |(r1 -> Mu0 f1)| and |(r2 -> Mu0 f2)|.

\subsection{Lexicographic recursion}
Some recursive functions over multiple recursive values
justify termination because their arguments decrease at every recursive call
under a lexicographic ordering.  Note that this different from
simultaneous iteration where each of the arguments decrease in
every recursive call. In a lexicographic ordering, some arguments may
either stay the same (in more significant positions) or even increase
(in less significant positions) while the other arguments decrease.
A typical example of lexicographic recursion is the Ackermann function,
which we can define using general recursion in Haskell as follows:
%format Nat_g = Nat"_g"
%format Zero_g = Zero"_g"
%format Succ_g = Succ"_g"
%format acker_g = acker"_g"
\begin{code}
data Nat_g = Zero_g | Succ_g Nat_g

acker_g Zero_g      n           = Succ_g n
acker_g (Succ_g m)  Zero_g      = Succ_g (acker_g m Zero_g)
acker_g (Succ_g m)  (Succ_g n)  = acker_g m (acker_g (Succ_g m) n)
\end{code}~\vspace*{-1.3em}\\
Observe that the first argument is more significant than the second.
In the third equation, the first argument |m| of the outer recursive call
decreases (\ie, smaller than |(Succ_g m)|) while the second argument
|(acker_g (Succ_g m) n)| may increase (\ie, may be larger than |(Succ_g n)|).

\begin{comment}
\begin{code}
int2natg 0 = Zero_g
int2natg n = Succ_g (int2natg (n-1))
natg2int Zero_g = 0
natg2int (Succ_g n) = 1 + natg2int n
ackerg n m = natg2int (acker_g (int2natg n) (int2natg m))
\end{code}
\end{comment}
The following Mendler-style recursion scheme captures the idea of
lexicographic recursion over two arguments.
%format mlexpr = "\textbf{mlexpr}"
%format mlexpr0 = mlexpr"_{*,*}"
\begin{code}
mlexpr0 :: (forall r1 r2  .   (r1 -> Mu0 f2 -> a)  -- outer recursive call
                          ->  (r2 -> a)            -- inner recursive call
                          ->  (r1 -> Mu0 f1)       -- cast1
                          ->  (r2 -> Mu0 f2)       -- cast2
                          ->  f1 r1 -> f2 r2 -> a) -> Mu0 f1 -> Mu0 f2 -> a

mlexpr0 phi (In0 x1) (In0 x2) = phi (mlexpr0 phi) (mlexpr0 phi (In0 x1)) id id x1 x2 
\end{code}~\vspace*{-1.3em}\\
The Mendler-style lexicograph recursion |mlexpr0| is similar to
the Mendler-style simultaneous recursion |msimpr0| introduced
in the previous section, but has two abstract operations for
inner and outer recursion. Note the types of these two recursive calls
|(r1 -> Mu0 f2 -> a)| and |(r2 -> a)|. The outer recursive call expects
its first argument to be a direct subcomponent by requiring its type to be |r1|.
The second argument has type |Mu0 f2|, which means that it could be any value,
because it is the less significant factor of the lexicographic ordering.
The inner recursive call only expects its second argument
to be a direct subcomponent by requiring its type to be |r2|.
Since the inner call assumes that the first argument stays the same,
the first argument is omitted. Using |mlexpr0|,
we can define the Ackermann function as follows:

\begin{code}
acker = mlexpr0 phi where
  phi ack ack' cast1 cast2 Zero      Zero      = succ zero
  phi ack ack' cast1 cast2 Zero      (Succ n)  = succ (succ (cast2 n))
  phi ack ack' cast1 cast2 (Succ m)  Zero      = succ (ack m zero)
  phi ack ack' cast1 cast2 (Succ m)  (Succ n)  = ack m (ack' n)
\end{code}~\vspace*{-1.3em}\\ \indent
The idea for |mlexpr0| originated in a conversation between Tarmo Uustalu
and Tim Sheard at the TYPES 2013 workshop (not published anywhere else
at the moment). We strongly believe that |mlexpr0| terminates for all
positive datatypes. The termination behavior for negative (or,
mixed-variant) datatypes needs further investigation.


