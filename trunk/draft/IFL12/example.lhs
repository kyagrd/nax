%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{TODO main example} \label{sec:example}

In this section we will write similar programs in Nax, Haskell, and Agda.
What we really want to focus on is the use of term indices to enforce
invariants of programs, we hope the use of several host-languages
makes this idea accessible to a larger audience.

We adopted the examples from Conor McBride's keynote talk [TODO cite]
at ICFP 2012.

a type preserving evaluator and a stack safe compiler for
a simple expression lagnauge.

Agda version 2.3.0.1

GHC version 7.4.1 (should work in 7.6.x too)


more than index preserving.
One of our goals is to distinguish the Nax
approach from other approaches, and to illustrate why this approach 
has certain advantages.

%include example_eval.lhs

%include example_glist.lhs

%include example_compile.lhs

