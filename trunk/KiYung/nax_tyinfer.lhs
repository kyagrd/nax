\chapter{Type Inference in Nax}\label{ch:naxTyInfer}

TODO TODO

\begin{align*}
&\textbf{Term}&
t,s&~::= ~ x          
    ~  || ~ \l x    . t 
    ~  || ~ t ~ s       
    ~  ||  \<let> x=s \<in> t
\\
&\textbf{Type (or, monotype)}&
A,B&~::= ~ A -> B
    ~  || ~ \iota
    ~  || ~ X
\\
&\textbf{Type scheme (or, polytype)}&
\sigma&~::= ~ \forall X.\sigma
       ~  || ~ A
\\
&\textbf{Typing context}&
\Gamma&~::= ~ \cdot 
       ~  || ~ \Gamma, x:\sigma \quad (x\notin \dom(\Gamma))
\end{align*}

