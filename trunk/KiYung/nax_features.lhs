\chapter{Introduction to Features of the Nax Language}\label{ch:naxFeatures}
This chapter provides an informal introduction to the Nax programming language.
We go through several distinct features of Nax, providing one or more examples
for each feature. Basic understanding of these features will be neccessary
to continue further discussions on design principles (Chapter \ref{ch:nax}) and
type inference (Chapter \ref{ch:naxTyInfer}) in the following chapters.

All the examples in this chapter run on our prototype implementation of Nax.
An example usually consists of several parts.
\begin{itemize}
\item Introducing data definitions to describe the data of interest.
Recursive data is introduced in two stages. We must be careful to separate
parameters from indices when using indices to describe static properties of
data.

\item Introduce macros, either by explicit definition, or by
automatic fixpoint derivation to limit the amount of explicit notation
that must be supplied by the programmer.

\item Write a series of definitions that describe how the data is to be
manipulated. Deconstruction of recursive data can only be performed with
Mendler-style combinators to ensure strong normalization.
\end{itemize}

\section{Two-level types}\label{2level}
Non recursive datatypes are introduced by the |data| declaration.
The data declaration can include arguments. The kind and separation of
arguments into parameters and a indices is inferred. For example, 
the three non-recursive data types, |Bool|, |Either|, and |Maybe|,
familiar to many functional programmers, are introduced by declaring
the kind of the type, and the type of each of the constructors.
This is similar to the way {\small GADT}s are introduced in Haskell.
\begin{singlespace}
\vspace*{0.1in}\noindent
\begin{tabular}{l||l||l}
\begin{minipage}[t]{.25\linewidth}
\begin{code}
data Bool : *
  where
  False  : Bool
  True   : Bool
\end{code}
\end{minipage}

& 

\begin{minipage}[t]{.30\linewidth}
\begin{code}
data Either : * -> * -> *
  where 
  Left  : a -> Either a b
  Right : b -> Either a b
\end{code}
\end{minipage}

&

\begin{minipage}[t]{.26\linewidth}
\begin{code}
data Maybe : * -> *
  where
  Nothing : Maybe a
  Just    : a -> Maybe a  
\end{code}
\end{minipage}
\end{tabular}
\vspace*{0.1in}
\end{singlespace}

Note the kind information (|Bool: *|) declares |Bool| to be a type,
(|Either: * -> * -> *|) declares |Either| to be a type constructor
with two type arguments, and (|Maybe: * -> *|) declares |Maybe| to be
a type constructor with one type argument.

To introduce a recursive type, we first introduce a non recursive datatype
that uses a parameter where the usual recursive components occur. By design,
normal parameters of the introduced type are written first (|a| in |L| below)
and the type argument to stand for the recursive component is written last
(the |r| of |N|, and the |r| of |L| below).
\begin{singlespace}
\vspace*{0.1in}\noindent
\begin{tabular}{l||l}
\begin{minipage}[t]{.45\linewidth}
\begin{code}
-- The fixpoint of |N| will 
-- be the natural numbers.

data N : * -> * where
  Zero  : N r
  Succ  : r -> N r
\end{code}
\end{minipage}

& 

\begin{minipage}[t]{.40\linewidth}
\begin{code}
-- The fixpoint of |(L a)| will 
-- be the polymorphic lists  

data L : * -> * -> * where
  Nil   : L a r
  Cons  : a -> r -> L a r
\end{code}
\end{minipage}
\end{tabular}
\vspace*{0.1in}
\end{singlespace}

A recursive type can be defined as the fixpoint of a (perhaps partially applied)
non-recursive type constructor. Thus the traditional natural numbers are typed
by |Mu[*] N| and the traditional lists with components of type |a| are typed by
|Mu[*] (L a)|.  Note that the recursive type operator |Mu[kappa]| is itself
specialized with a kind argument inside square brackets (|[ kappa ]|).
The recursive type (|Mu[kappa] f|) is well kinded only if the operand |f| has
kind |kappa -> kappa|, in which case the recursive type (|Mu[k] f|) has kind
|kappa|. Since both |N| and |(L a)| have kind |* -> *|, the recursive types
|Mu[*] N| and |Mu[*] (L a)| have kind |*|. That is, they are both types,
not type constructors.

\section{Creating values}

Values of a particular data type are created by use of constructor functions.
For example |True| and |False| are nullary constructors (or, constants) of
type |Bool|. |(Left 4)| is a value of type |(Either Int a)|. Values of
recursive types (\ie, those values with types such as |(Mu[k] f)| are formed by
using the special |In[kappa]| constructor expression. Thus |Nil| has type |L a|
and |(In[*] Nil)| has type |(Mu[*] (L a))|. In general, applying the operator
|In[k]| injects a term of type |f(Mu[k] f)| to the recursive type |(Mu[k] f)|.
Thus a list of |Bool| could be created using the term
|(In[*] (Cons True (In[*] (Cons False  (In[*] Nil)))))|. 
A general rule of thumb, is to apply |In[k]| to terms of non-recursive type
to get terms of recursive type. Writing programs using two level types, and
recursive injections has definite benefits, but it surely makes programs rather
annoying to write. Thus, we have provided Nax with a simple but powerful
synonym (macro) facility.

\section{Synonyms, constructor functions, and fixpoint derivation}
\label{macro}

We may codify that some type is the fixpoint of another, once and for all,
by introducing a type synonym (macro).

\begin{code}
synonym Nat = Mu[*] N
synonym List a = Mu[*] (L a)     
\end{code}

In a similar manner we can introduce constructor functions that create
recursive values without explicit mention of |In| at their call sites
(potentially many), but only at their site of definition (exactly once).

\begin{code}
zero    = In[*] Zero
succ n  = In[*] (Succ n)

nil        = In[*] Nil
cons x xs  = In[*] (Cons x xs)
\end{code}

This is such a common occurrence that recursive synonyms and
recursive constructor functions can be automatically derived.
Automatic synonym and constructor derivation using Nax is
both concise and simple. The clause ``|deriving fixpoint List|" (below right)
causes the |synonym| for |List| to be automatically defined.
It also defines the constructor functions |nil| and |cons|.  By convention,
the constructor functions are named by dropping the initial upper-case letter
in the name of the non-recursive constructors to lower-case.  To illustrate,
we provide side-by-side comparisons of Haskell and two different uses of Nax.

\begin{singlespace}
\vspace*{0.1in}\noindent
\begin{tabular}{l || l || l}
{\em Haskell}  & {\em Nax with synonyms} &  {\em Nax with derivation} \\ \hline
\hskip-2em\begin{minipage}[t]{.35\linewidth}\small
\begin{code}
data List a 
  =  Nil 
  |  Cons a (List a)
{-" "-}
{-" "-}
{-" "-}
{-" "-}
x = Cons 3 (Cons 2 Nil)  
\end{code}
\end{minipage}

& 
\hskip-1.5em
\begin{minipage}[t]{.40\linewidth}\small
\begin{code}
data L: * -> * -> * where
  Nil  : L a r
  Cons : a -> r -> L a r
  
synonym List a = Mu[*] (L a)

nil        = In[*] Nil
cons x xs  = In[*] (Cons x xs)

x = cons 3 (cons 2 nil)  
\end{code}
\end{minipage}

&

\hskip-1.5em
\begin{minipage}[t]{.35\linewidth}\small
\begin{code}
data L: * -> * -> * where
   Nil  : L a r
   Cons : a -> r -> L a r
 deriving fixpoint List
{-" "-}
{-" "-}
{-" "-}
x = cons 3 (cons 2 nil)    
\end{code}
\end{minipage}

\end{tabular}
\end{singlespace}

\section{Mendler combinators for non-indexed types}
There are no restrictions on what kind of datatypes
can be defined in Nax. There are also no restrictions on the creation
of values. Values are created using constructor functions, and
the recursive injection (|In[k]|). 
To ensure strong normalization, analysis of constructed
values has some restrictions. Values of non-recursive types can
be freely analysed using pattern matching. Values of recursive types
must be analysed using one of the Mendler-style combinators. By design,
we limit pattern matching to values of non-recursive types, by
{\em not} providing any mechanism to match against
the recursive injection (|In[k]|).

To illustrate simple pattern matching over non-recursive types, we 
give a Nax multi-clause definition 
for the |not| function over the (non-recursive) |Bool| type,
and a function that strips off the |Just| constructor over the (non-recursive)
|Maybe| type using a case expression.
\begin{singlespace}
\vspace*{.1in}
\begin{tabular}{l || l}
\begin{minipage}[l]{.32\linewidth}
\begin{code}
not True   = False
not False  = True
\end{code}
\end{minipage}

& 

\begin{minipage}[l]{.40\linewidth}
\begin{code}
unJust0 x =  casei{} x of  Just x   -> x
                           Nothing  -> 0
\end{code}
\end{minipage}
\end{tabular}
\vspace*{.1in}
\end{singlespace}

Analysis of recursive data is performed with Mendler-style combinators. In our
implementation we provide 5 Mendler-style combinators:
 |MIt| (fold or catamorphism or iteration),
 |MPr| (primitive recursion),
 |McvIt| (courses of values iteration), and
 |McvPr| (courses of values primitive recursion), and
 |MsfIt| (fold or catamorphism or iteration for recursive types with negative occurrences).

A Mendler-style combinator is written in a manner similar to a case expression.
A Mendler-style combinator expression contains patterns, and the variables bound in the patterns
are scoped over a term. This term is executed if the pattern matches. 
A mendler-style combinator expression differs from a case expression
in that it also introduces additional names (or variables) into scope.
These variables play a role similar in nature to the operations of
an abstract datatype, and provide additional functionality in addition to what can be
expressed using just case analysis.

For a visual example, compare the |case| expression to the |MIt| expression.
In the |case|, each {\em clause} following the |of| indicates a possible match
of the scrutinee |x|. In the |MIt|, each {\em equation} following the |with|,
binds the variable $\newFi{f}$, and matches the pattern to a value related to
the scrutinee |x|.

\begin{singlespace}
%{
%format e1
%format e2
\vspace*{.1in}\noindent
\begin{tabular}{l || l}
\begin{minipage}[t]{.42\linewidth}
\begin{code}
casei{} x of  Nil        -> e1
              Cons x xs  -> e2
\end{code}
\end{minipage}

& 

\begin{minipage}[t]{.50\linewidth}
\begin{code}
MIt{} x with  (NEWFI f) (Cons x xs)  =  e1
              (NEWFI f) Nil          =  e2
\end{code}
\end{minipage}
\end{tabular}
\vspace*{.1in}
%}
\end{singlespace}

The number and type of the additional variables depends upon which family of
Mendler combinators is used to analyze the scrutinee.  Each equation specifies
(a potential) computation in an abstract datatype depending on whether
the pattern matches. For the |MIt| combinator (above) the abstract datatype
has the following form. The scrutinee, |x| is a value of some recursive type
|(Mu[*] T)| for a non-recursive type constructor |T|. In each clause,
the pattern has type |(T r)|, for some abstract type |r|. The additional
variable introduced ($\newFi{f}$) is an operator over the abstract type, |r|,
that can safely manipulate only abstract values of type |r|.

Different Mendler-style combinators are implemented by different abstract types.
Each abstraction safely describes a class of provably terminating computations 
over a recursive type. The number (and type) of abstract operations differs from
one family of Mendler combinators to another. We give descriptions of three
families of Mendler combinators, their abstractions, and the types of
the operators within the abstraction, below. In each description, the type
|ans| represents the result type, when the Mendler combinator is fully applied.
\begin{singlespace}
%{
%format p_i
%format e_i
\vspace*{.1in}\noindent
\begin{tabular}{l || l || l}
\hskip-2em
\begin{minipage}[t]{.31\linewidth}
\begin{code}
MIt{} x with
  (NEWFI f) p_i = e_i
{-" "-}
x    : Mu[*] T
f    : r -> ans
{-" "-}
p_i  : T r
e_i  : ans
{-" "-}
MIt{psi} phi (In[*] x) 
   = phi (MIt{psi} phi) x
\end{code}   
\end{minipage}
& 
\hskip-1.5em
\begin{minipage}[t]{.38\linewidth}
\begin{code}
MPr{} x with
  (NEWFI f) (NEWFI cast) p_i = e_i
{-" "-}
x    : Mu[*] T
f    : r -> ans
cast : r -> Mu[*] T
p_i  : T r
e_i  : ans
{-" "-}
MPr{psi} phi (In[*] x) 
  = phi (MPr{psi} phi) (In[*]) x
\end{code}  
\end{minipage}

& 
\begin{minipage}[t]{.28\linewidth}
\begin{code}
McvIt{} x with
  (NEWFI f) (NEWFI project) p_i = e_i
{-" "-}
x        : Mu[*] T
f        : r -> ans
project  : r -> T r
p_i      : T r
e_i      : ans
{-" "-}
McvIt{psi} phi (In[*] x) 
    = phi (McvIt{psi} phi) out x
  where out (In[*] x) = x
\end{code}
\end{minipage}

\end{tabular}
\vspace*{.1in}
%}
\end{singlespace}

A Mendler-style combinator implements a (provably terminating) recursive function
applied to the scrutinee. The abstract type and its operations ensure
termination. Note that every operation above includes an abstract operator,
|f: r -> ans|. This operation represents a recursive call in the function
defined by the Mendler-style combinator. Other operations, such as |cast| and |project|,
support additional functionality within the abstraction in which they are
defined (|MPr| and |McvIt| respectively).  The equations at the bottom of
each section provide an operational understanding of how the operator works.
These can be safely ignored until after we see some examples of how
a Mendler-style combinator works in practice.
\begin{singlespace}
\begin{code}
length y     = MIt{} y    with  len Nil          = zero
                                len (Cons x xs)  = (succ zero) + len xs
                          
tail x       = MPr{} x    with  tl cast Nil          = nil
                                tl cast (Cons y ys)  = cast ys
                          
factorial x  = MPr{} x    with  fact cast Zero      = succ zero
                                fact cast (Succ n)  = times (succ (cast n)) (fact n)
                          
fibonacci x  = McvIt{} x  with  fib out Zero      =  succ zero
                                fib out (Succ n)  =  casei{} (out n) of
                                                       Zero    -> succ zero
                                                       Succ m  -> fib n + fib m 
\end{code}
\end{singlespace}

The |length| function uses the simplest kind of recursion where
each recursive call is an application to a direct subcomponent of the input.
Operationally, |length| works as follows. The scrutinee, |y|,
has type |(Mu[*] (L a))|, and has the form |(In[*] x)|. 
The type of |y| implies that |x| must have the form |Nil| or
|(Cons x xs)|.  The |MIt| strips off the |In[*]| and matches |x| against
the |Nil| and |(Cons x xs)| patterns. If the |Nil| pattern matches, then
|0| is returned. If the |(Cons x xs)| pattern matches, |x| and |xs| are bound.
The abstract type mechanism gives the pattern |(Cons x xs)| the type |(L a r)|,
so (|x: a|) and (|xs: r|) for some abstract type |r|. The abstract operation,
(|len: r -> Int|), can safely be applied to |xs|, obtaining the length of
the tail of the original list. This value is incremented, and then returned.
The |MIt| abstraction provides a safe way to allow the user to make
recursive calls, |len|, but the abstract type, |r|, limits its use to
direct subcomponents, so termination is guaranteed.

Some recursive functions need direct access, not only to the direct
subcomponents, but also the original input as well. The Mendler-style combinator
|MPr| provides a safe, yet abstract mechanism, to support this. The Mendler
|MPr| abstraction provides two abstract operations. The recursive caller with
type (|r -> ans|) and a casting function with type (|r -> Mu[k] T|).
The casting operation allows the user to recover the original type from
the abstract type |r|, but since the recursive caller only works on
the abstract type |r|, the user cannot make a recursive call on one of these
cast values. The functions |factorial| (over the natural numbers) and
|tail| (over lists) are both defined using |MPr|.

Note how in |factorial| the original input is recovered (in constant time) by
taking the successor of casting the abstract predecessor, |n|. In the |tail|
function, the abstract tail, |ys|, is cast to get the answer, and
the recursive caller is not even used.

Some recursive functions need direct access, not only to the direct
subcomponents, but even deeper subcomponents. The Mendler-style combinator |McvIt|
provides a safe, yet abstract mechanism, to support this.
The function |fibonacci| is a classic example of this kind of recursion.
The Mendler |McvIt| provides two abstract operations. The recursive caller
with type (|r -> ans|) and a projection function with type (|r -> T r|).
The projection allows the programmer to observe the hidden |T| structure
inside a value of the abstract type |r|.  In the |fibonacci| function above,
we name the projection |out|. It is used to observe if the abstract predecessor,
|n|, of the input, |x|, is either zero, or the successor of
the second predecessor, |m|, of |x|. Note how recursive calls are made on
the direct predecessor, |n|, and the second  predecessor, |m|.

Each recursion combinator can be defined by the equation at the bottom of
its figure.  Each combinator can be given a naive type involving
the concrete recursive type (|Mu[*] T|), but if we instead give it
a more abstract type, abstracting values of type (|Mu[*] T|) into some
unknown abstract type |r|, one can safely guarantee a certain pattern of
use that insures termination.  
Informally, if the combinator works for some unknown type |r| it will certainly
also work for the actual type (|Mu[*] T|), but because it cannot assume that
|r| has any particular structure, the user is forced to use the abstract
operations in carefully proscribed ways.
  
\section{Types with static indices}\label{sec:bg:ixty}
Recall that a type can have both parameters and indices, and that indices
can be either types or terms. We define three types below each with one or more
indices. Each example defines a non-recursive type, and then uses derivation to
define synonyms for its fix point and recursive constructor functions.
By convention, in each example, the argument that abstracts the recursive
components is called |r|. By design, arguments appearing before |r| are
understood to be parameters, and arguments appearing after |r| are understood
to be indices. To define a recursive type with indices, it is necessary to
give the argument, |r|, a higher-order kind. That is, |r| should take indices
as well, since it abstracts over a recursive type which takes indices.
\begin{singlespace}
\begin{code}
data Nest: (* -> *) -> * -> * where
   Tip   : a -> Nest r a
   Fork  : r(a,a) -> Nest r a
     deriving fixpoint PowerTree
  
data V: * -> (Nat -> *) -> Nat -> * where
  Vnil   : V a r {`zero}
  Vcons  : a -> r {n} -> V a r {`succ n}
    deriving fixpoint Vector

data Tag = E | O

data P: (Tag -> Nat -> *) -> Tag -> Nat -> * where
  Base   : P r {E} {`zero} 
  StepO  : r {O} {i} -> P r {E} {`succ i}
  StepE  : r {E} {i} -> P r {O} {`succ i}
    deriving fixpoint Proof
\end{code}
\end{singlespace}
Note, to distinguish type indices from term indices (and to make parsing
unambiguous), we enclose term indices in braces (|{ ... }|). We also
backquote (|`|) variables in terms that we expect to be bound in
the current environment. Un-backquoted variables are taken to be
universally quantified. By backquoting |succ|, we indicate that we want terms,
which are applications of the successor function, but not some universally
quantified function variable\footnote{In the design of Nax we had a choice.
Either, explicitly declare each universally quantified variable, or explicitly
mark those variables not universally quantified. Since quantification is much
more common than referring to variables already in scope, the choice was easy.}.
For non-recursive types without parameters, the kind of the fixpoint is
the same as the kind of the recursive argument |r|. If the non-recursive type
has parameters, the kind of the fixpoint will be composed of the parameters
|->| the kind of the recursive argument |r|. For example, study the kinds of
the fixpoints for the non-recursive types declared above in the table below.
\begin{center}
\begin{tabular}{l||c||c||c}
non-recursive type & |Nest|        & |V|                & |P|        \\
recursive type     & |PowerTree|   & |Vector|           & |Proof|    \\ \hline
kind of |T|        & |* -> *|      & |* -> Nat -> *|    & |Tag -> Nat -> *|  \\ 
kind of |r|        &  |* -> *|     & |Nat -> *|         & |Tag -> Nat -> *|  \\
number of parameters  & 0             & 1                  & 0                  \\ 
number of indices     & 1 (type)      & 1 (term)           & 2 (term,term)
\end{tabular}
\end{center}
Recall, indices are used to track static properties about values
with those types. A well-formed (|PowerTree x|) contains a balanced
set of parenthesized binary tuples of elements. The index, |x|, describes
what kind of values are nested in the parentheses. The invariant is that the
number of items nested is always an exact power of 2. A (|Vector a {n}|) is
a list of elements of type |a|, with length exactly equal to |n|, and
a (|Proof {E} {n}|) witnesses that the natural number |n| is even, and
a (|Proof {O} {m}|) witnesses that the natural number |m| is odd.
Some example value with these types are given below.

\begin{code}
tree1  : PowerTree Int = tip 3
tree2  : PowerTree Int = fork (tip (2, 5))
tree3  : PowerTree Int = fork (fork (tip ((4, 7), (0, 2))))

v2 : Vector Int {succ (succ zero)} = (vcons 3 (vcons 5 vnil))

p1  : P {O} {succ zero}         = stepE base
p2  : P {E} {succ (succ zero)}  = stepO (stepE base)
\end{code}

Note that in the types of the terms above, the indices in braces (|{ ... }|)
are ordinary terms (not types).  In these example we use natural numbers (\eg,
|succ (succ zero)|) and elements (|E| and |O|) of the two-valued type |Tag|.
It is interesting to note that sometimes the terms are of recursive types (\eg,
|Nat| which is a synonym for |Mu[*] N|), and some are non-recursive types (\eg,
|Tag|).


\section{Mendler-style combinators for indexed types}

Mendler-style combinators generalize naturally to indexed types. The key observation
that makes this generalization possible is that the types of the operations
within abstraction have to be generalized to deal with the type indices in
a consistent manner. How this is done is best first explained by example, and
then later abstracted to its full general form.

Recall, a value of type (|PowerTree Int|) is a set of integers. This
set is constructed as a balanced binary tree with pairs at the leaves
(see {\it tree2} and {\it tree3} above).
The number of integers in the set is an exact power of 2. Consider
a function that adds up all those integers. One wants a function of type
(|PowerTree Int -> Int|). One strategy to writing this function is to write
a more general function of type (|PowerTree a -> (a -> Int) -> Int|). In Nax,
we can do this as follows:
\begin{singlespace}
\begin{code}
genericSum t =  MIt { a . (a -> Int) -> Int } t with
                  sum (Tip x)   = \ f -> f x
                  sum (Fork x)  = \ f -> sum x (\ (a,b) -> f a + f b)

sumTree t = genericSum t (\ x -> x)
\end{code}
\end{singlespace}
In general, the type of the result of a function over an indexed type,
can depend upon what the index is. Thus, a Mendler-style combinator over a value
with an indexed type, must be type-specialized to that value's index.
Different values of the same general type, will have different indices.
After all, the role of an index is to witness an invariant about the value,
and different values might have different invariants. Capturing this variation
is the role of the  clause |{a . (a -> Int) -> Int}| following the keyword
|MIt|. We call such a clause, an \emph{index transformer}. In the same way
that the type of the result depends upon the index, the type of the different
components of the abstract datatype implementing the Mendler-style combinator
also depend upon the index. In fact, everything depends upon the index
in a uniform way. The index transformer captures this uniformity.
One cannot abstract over the index transformer in Nax. Each Mendler-style combinator,
over an indexed type, must be supplied with a concrete clause (inside
the braces) that describe how the results depend upon the index.  To see how
the transformer is used, study the types of the terms in the following paragraph.
Can you see the relation between the types and the transformer?

The scrutinee |t| has type (|PowerTree a|) which is a synonym for
(|(Mu[* -> *] Nest) a|). The recursive caller |sum| has type
(|forall a. r a -> (a -> Int) -> Int|), for some abstract type constructor |r|.
Recall |r| has an index, so it must be a type constructor, not a type. 
The patterns (|Tip x|) and (|Fork x|) have type (|Nest r a|) and
the right hand sides of the equations: (|\ f -> f x|) and
(|\ f -> sum x (\ (a,b) -> f a + f b)|), have type (|(a -> Int) -> Int|).
Note that the dependency of (|(a -> Int) -> Int|) on the index |a|, appears in
both the result type, and the type of the recursive caller. If we think of
an index transformer, like |{a . (a -> Int) -> Int}|, as a function:
|psi a = (a -> Int) -> Int|, we can succinctly describe the types of
the abstract operations in the |MIt| Mendler abstraction.
In the table below, we put the general case on the left, and
terms from the |genericSum| example, that illustrate the general case,
on the right.
%{
%format p_i
%format e_i
\vspace*{0.1in}\noindent
\begin{singlespace}
\begin{code}
MIt{psi} x with
  f p_i = e_i
\end{code}
\end{singlespace}
\begin{tabular}{l||clcl}
|psi : kappa -> *|               & & |{a . (a -> Int) -> Int}| & : & |* -> *| \\
|T : (kappa -> *) -> kappa -> *| & & |Nest| & : & |(* -> *) -> * -> *| \\
|x : (Mu[kappa -> *] T) a|   & & |t|    & : & |(Mu[* -> *] Nest) a| \\
|f : forall (a : kappa) . r a -> psi a| & & |sum| & : & |forall (a : *). r a -> (a -> Int) -> Int| \\
|p_i : T r a| & & |Fork x|     & : & |Nest r a| \\
|e_i : psi a| & & |\ f -> f x| & : & |(a -> Int) -> Int| \\
\end{tabular}
\vspace*{0.1in}
%}

The same scheme for |MIt| generalizes to type constructors with term indices,
and with multiple indices. To illustrate this we give the generic schemes for
type constructors with 2 or 3 indices. In the table the variables |kappa1|,
|kappa2|, and |kappa3|, stand for arbitrary kinds (either kinds for types,
like |*|, or kinds for terms, like |Nat| or |Tag|).
\begin{center}
%{
%format p_i
%format e_i
\begin{tabular}{l||l}
\hskip-5em
\begin{minipage}[l]{.55\linewidth}
\begin{code}
T    : (kappa1 -> kappa2 -> *) -> (kappa1 -> kappa2 -> *)
psi  : kappa1 -> kappa2 -> *
x    : (Mu[kappa1 -> kappa2 -> *] T) a b
f    : forall (a:kappa1)(b:kappa2) . r a b -> psi a b
p_i  : T r a b
e_i  : psi a b
\end{code}
\end{minipage}

&
\begin{minipage}[l]{.45\linewidth}
\begin{code}
T    : (kappa1 -> kappa2 -> kappa3 -> *) -> (kappa1 -> kappa2 -> kappa3 -> *)
psi  : kappa1 -> kappa2 -> kappa3 -> *
x    : (Mu[kappa1 -> kappa2 -> kappa3 -> *] T) a b c
f    : forall (a:kappa1)(b:kappa2)(c:kappa3) . r a b c -> psi a b c
p_i  : T r a b c
e_i  : psi a b c
\end{code}
\end{minipage}
\end{tabular}
%}
\end{center}
The simplest form of index transformation, is where the transformation
is a constant function. This is the case of the function that computes
the integer length of a natural-number, length-indexed, list
(what we called a |Vector|). Independent of the length the result
is an integer. Such a function has type: |Vector a {n} -> Int|.
We can write this as follows:
\begin{singlespace}
\begin{code}
vlen x =  MIt{{i} . Int} x with  len Vnil          = 0
                                 len (Vcons x xs)  = 1 + len xs
\end{code}
\end{singlespace}

Let's study an example with a more interesting index transformation.
A term with type (|Proof {E} {n}|), which is synonymous with the type 
(|Mu[Tag -> Nat -> *] P {E} {n}|), witnesses that the term |n| is even.
Can we transform such a term into a proof that |n+1| is odd?  We can
generalize this by writing a function which has both of the types below: \\
|Proof {E} {n} -> Proof {O} {`succ n}|,  and \\
|Proof {O} {n} -> Proof {E} {`succ n}|. \\
We can capture this dependency by defining the term-level function |flip|,
and using an |MIt| with the index transformer:
|{{t} {i} . Proof {`flip t} {`succ i}}|.
\begin{singlespace}
\begin{code}
flip E = O
flip O = E

flop x =  MIt {{t} {i} . Proof {`flip t} {`succ i}} x with
            f Base       = stepE base
            f (StepO p)  = stepE(f p)
            f (StepE p)  = stepO(f p)
\end{code}
\end{singlespace}

For our last term-indexed example, every length-indexed list has a length,
which is either even or odd. We can witness this fact by writing a function
with type: |Vector a {n} -> Either (Even {n}) (Odd {n})|.
Here, |Even| and |Odd| are synonyms for particular kinds of |Proof|.
To write this function, we need the index transformation:
|{ {n} . Either (Even {n}) (Odd {n}) }|.
\begin{singlespace}
\begin{code}    
synonym Even  {x} = Proof {E} {x}
synonym Odd   {x} = Proof {O} {x}

proveEvenOrOdd x =  MIt { {n} . Either (Even {n}) (Odd {n})} x with
                      prEOO Vnil          =  Left base
                      prEOO (Vcons x xs)  =  casei{} prEOO xs of
                                               Left p   -> Right(stepE p)
                                               Right p  -> Left(stepO p)  
\end{code}
\end{singlespace}

\section{Recursive types of unrestricted polarity but restricted elimination}
\label{sec:bg:recty}
In Nax, programmers can define recursive data structures with both positive and 
negative polarity.  The classic example is a datatype
encoding the syntax of $\lambda$-calculus, which uses higher-order abstract syntax (HOAS).
Terms in the $\lambda$-calculus are either variables, applications, or abstractions.
In a HOAS representation, one uses Nax functions to encode abstractions. We
give a two level description for recursive $\lambda$-calculus |Term|s, by taking
the fixpoint of the non-recursive |Lam| datatype. 
\begin{singlespace}
\begin{code}    
data Lam : * -> * where
  App  :: r -> r -> Lam r
  Abs  :: (r -> r) -> Lam r
    deriving fixpoint Term
 
apply = abs (\ f -> abs (\ x -> app f x)) 
\end{code}
\end{singlespace}
Note that we don't need to include a constructor for variables,
as variables are represented by Nax variables, bound by Nax
functions. For example the lambda term: ($\lambda f . \lambda x . f\; x$)
is encoded by the Nax term |apply| above.

Note also, the recursive constructor: |abs: (Term -> Term) -> Term|,
introduced by the |deriving fixpoint| clause, has a negative occurrence of
the type |Term|. In a language with unrestricted analysis, such a type could
lead to non-terminating computations. The Mendler |MIt| and |MPr| combinators
limit the analysis of such types in a manner that precludes non-terminating
computations. The Mendler-style combinator, |McvIt|, is too expressive to exclude
non-terminating computations, and must be restricted to recursive datatypes
with no negative occurrences.

Even though |MIt| and |MPr| allow us to safely operate on values of type |Term|,
they are not expressive enough to write many interesting functions. Fortunately,
there is a more expressive Mendler-style combinator that is safe over
recursive types with negative occurrences. We call this combinator |MsfIt|.
This combinator is based upon an interesting programming trick, first described
by Sheard and Fegaras \cite{FegShe96}, hence the ``\textsf{sf}'' in the name
|MsfIt|.  The abstraction supported by |MsfIt| is as follows:
\begin{singlespace}
\begin{center}
%{
%format p_i
%format e_i
\begin{tabular}{l||l}
\begin{minipage}[t]{.30\linewidth}
\begin{code}
MsfIt{} x with
  f inv p_i = e_i
\end{code}
\end{minipage}
&
\begin{minipage}[t]{.30\linewidth}
\begin{code}
x    : Mu[*] T
f    : r -> ans
inv  : ans -> r
p_i  : T r
e_i  : ans
\end{code}
\end{minipage}
\end{tabular}
%}
\end{center}
\end{singlespace}

To use |MsfIt| the inverse allows one to cast an answer into an abstract value.
To see how this works, study the function that turns a |Term| into a string.
The strategy is to write an auxiliary function, |showHelp| that takes an extra
integer argument. Every time we encounter a lambda abstraction, we create a
new variable, \texttt{x}$n$ (see the function |new|), where $n$ is the current
value of the integer variable. When we make a recursive call, we increment
the integer. In the comments (the rest of a line after |--|), we give
the type of a few terms, including the abstract operations |sh| and |inv|.
\begin{singlespace}
\begin{code}
                          {-" "-} -- |cat           : List String -> String|
                          {-" "-} -- |new           : Int -> String|
new n = cat["x",show n]   {-" "-}
                          {-" "-} -- |showHelp      : Term -> (Int -> String)|
                          {-" "-} -- |sh            : r -> (Int -> String)|
                          {-" "-} -- |inv           : (Int -> String) -> r|
                          {-" "-} -- |(\ n -> new m): Int -> String|
showHelp x =
   MsfIt{} x with 
    sh inv (App x y)  = \ m -> cat [  "(", sh x m, " ", sh y m, ")"]
    sh inv (Abs f)    = \ m -> cat [  "(fn ", new m, " => ",
                                      sh (f (inv (\ n -> new m))) (m+1), ")"]
showTerm x = showHelp x 0

showTerm apply : List Char = "(fn x0 => (fn x1 => (x0 x1)))"
\end{code}
\end{singlespace}
The final line of the example above illustrates applying |showTerm| to |apply|.
Recall that |apply = abs (\ f -> abs (\ x -> app f x))|, which is the HOAS
representation of the $\lambda$-calculus term ($\lambda f . \lambda x . f\; x$).

\section{Lessons from Nax}

Nax is our first attempt to build a strongly normalizing, sound and consistent
logic, based upon Mendler-style iteration. We would like to
emphasize the lessons we learned along the way.

\begin{itemize}
\item Writing types as the fixed point of a non-recursive type constructor
is quite expressive. It supports a wide variety of types including
the regular types (|Nat| and |List|), nested types (|PowerTree|),
{\small GADT}s (|Vector|), and mutually recursive types (|Even| and |Odd|).

\item Two-level types, while expressive, are a pain to program with (all those
|Mu[kappa]| and |In[kappa]| annotations), so a strong synonym or macro
facility is necessary. With syntactic support, one hardly even notices.

\item The use of term-indexed types allows programmers to write types that
act as logical relations, and form the basis for reasoning about programs.
In Chapters \ref{ch:fi} and \ref{ch:fixi}, we have formalized lambda calculi,
which support term indices.
 
\item Using Mendler-style combinators is expressive, and with syntactic support
(the |with| equations of the Mendler combinators), is easy to use. In
fact Nax programs are often no more complicated than their Haskell counterparts.

\item Type inference is an important feature of a programming language. We
hope you noticed, that apart from index transformers, no type information
is supplied in any of the Nax examples. The Nax compiler reconstructs
all type information.

\item Index transformers are the minimal information needed to extend 
Hindley-Milner type inference over GADTs. One can always predict
where they are needed, and the compiler can enforce that the
programmer supplies them. They are never needed for non-indexed types.
Nax faithfully extends Hindley-Milner type inference.
\end{itemize}


