---
title: Solving Counting Constraints on First Order Formulas in SMT
date: August 28, 2016
numbersections: true
subparagraph: true
secnumdepth: 2
link-citations: true
toc: true
header-includes:
  - \usepackage{tikz}
  - \usepackage{bussproofs}
  - \usepackage{syntax}
  - \usepackage{amsthm}
  - \usepackage{color}
  - \let\oldhl\hyperlink 
  - \usepackage{algorithm}
  - \usepackage[noend]{algpseudocode}
  - \setcounter{secnumdepth}{3}
---
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}
\newtheorem{property}{Property}

# Introduction {-}

TODO

# Model Checking of parametrized and fault tolerant systems

TODO

## Counting Constraints

Model checking usually relies on checking that the negation of a property is
unsatisfiable. Properties and transitions can be expressed with first order
formulas, with or without quantifiers. This problem is known to be undecidable @apt1986limits, that is why it is crucial to understand what is the class of formulas used to specify them, and to restrict them if possible.

Counting constraints provide a way to specify how many integers satisfy a given
predicate. Thus, it is a generalization of quantifiers over the integers. For
instance, if $a$
is an array of booleans of size $n$, the counting constraint $\sharp\{ x \ |\ a[x]\} > n/2$
specify that more than half the array is set to `true`. An existential
quantifier can be transformed into a constraint involving a cardinality greater
than 1, and a universal quantifier into a counting constraint composed of a
cardinality equal to 0 (in this case, the predicate will be the negation of the
formula).

For the class of problems we want to study, they are very adapted to express properties of the systems, such as the maximum fraction of faulty components. However, dealing with several nested quantifiers is hard, and a
lot of problems can be modeled with a single level of quantification (i.e. there
is no nested counting constraints terms inside other counting constraints). Thus, this
problem can be restricted to this case and still be interesting, and provides a
simplified version of quantifiers, while avoiding the requirement to support a
more complete class of formulas. SMT formulas with a lot of quantifiers are indeed known to  be hard to solve
\cite{ge2009complete}.

# Solving Counting Constraints for Arithmetic

## Syntax

We consider a set of distinct theories $\mathbf{T}_\mathbb{Z}$,
$\mathbf{T}_{eq}$,
$\mathbf{T}_2$, …, $\mathbf{T}_n$, where $\mathbf{T}_\mathbb{Z}$ is the theory
of $\mathbb{Z}$, and $\mathbf{T}_{eq}$ is the theory of equality between the other theory.
Atoms and variables of these theories are defined as usual. In the following, a first order formula without quantifiers is defined with the grammar \ref{formula}. The terms of the form
$c = \sharp\{ x\ |\ \psi(x) \}$ are called counting constraints. Here,
$\sharp\{ x\ |\ \psi(x)\}$ denotes the cardinality of a subset $S$ of $\mathcal{Z}$ such as
$x \in S \iff \psi(x)$.

\begin{figure}[h]
\begin{grammar}
	
<formulas> $\phi$ ::= $\phi$ $\land$ $\phi$
\alt $\phi$ $\lor$ $\phi$
\alt $\lnot$ $\phi$
\alt <atoms> of $\mathbf{T}_i$
\alt $c = \sharp\{ x\ |\ \psi(x) \}$ where $c$ is a variable of $\mathbf{T}_\mathbb{Z}$

<counting constraints> $\psi(x)$ ::= $\psi(x)$ $\land$ $\psi(x)$
\alt $\psi(x)$ $\lor$ $\psi(x)$
\alt $\lnot$ $\psi(x)$
\alt <atoms> of $\mathbf{T}_i$ where $x$ does not appear
\alt $x \leq y$ where $y$ is a variable of $\mathbf{T}_\mathbb{Z}$
\alt $y \textless x$ where $y$ is a variable of $\mathbf{T}_\mathbb{Z}$


\end{grammar}
\caption{Formula syntax}
\label{formula}
\end{figure}

We consider a subclass of the formulas built on the syntax of Figure \ref{formula}, formulas of the form:
\begin{equation}
F(c_1, …, c_n, \mathbf{y}) \land \bigwedge\limits_{i=1}^n c_i = \sharp\{ x \ |\ \psi_i(x, c_1, …, c_n,
\mathbf{y})\}
\label{maingoal}
\end{equation}

where no counting constraints appear in $F$. While most formulas can be
rewritten to this form, there are some corner cases\footnote{If $\{x\ |\ \phi(x)\}$ is infinite, then $c = \sharp\{x\ |\ \phi(x)\}$ is necessarily `unsat`, and the semantics of $true \lor c = \sharp\{x\ |\ \phi(x)\}$ is unclear. In practice, we only deal with finite intervals, so we are not interested in those cases.}.

We are going to explain a way to decide this formula, i.e. saying wether they
are satisfiable, and if yes give a model that satisfies this formula.

We assume that we already have a solver to solve formulas without counting
constraints (which can give a model if the formula is `sat`).

In @AlbertiGP16 and @schweikardt, there is already a way to solve those formula.
However, while they definitively explain that the problem is decidable and why, they heavily rely on quantifier elimination and thus may not be very practical nor easily integrated in modern SMT solvers.

\ 

To solve a counting constraint $c = \sharp\{x\ |\ \phi{x}\}$, our algorithm symbolically computes the set $\{x\ |\ \phi{x}\}$ and express it size with an arithmetic formula. To do that, it needs to make additional assumptions on the formula free variables.

## Constraints Interpretation

Definition[Assumptions]:
We call assumptions a set $A$ whose elements are atoms of the theories $\mathbf{T}_i$. In the context of a first order formula, writing $A$ means the conjuctions of the atoms of $A$.

Definition[Symbolic Interval]:
A symbolic interval is a couple of values that are either arithmetic variables,
constants or $\infty$.
If $I = [a, b)$, $x \in I$ is defined as $x < b \land a \le x$.
\newline\ \newline
It is said to be finite if none of the bounds are infinite.

Definition[Arithmetic Domain]:
An arithmetic domain is a finite set of symbolic intervals (definition
\ref{symbolic}). It is usually associated to
some assumptions (definition \ref{assumptions}) which make them disjoint and
ensure that the lower bound of an interval is actually lower than the upper
bound.


If S is an arithmetic domain, we abusively write $x \in S$ for $\left(\bigvee\limits_{I \in S} x \in I\right)$.
We are going to prove that $(S, A) \vdash \phi(x, \mathbf{y})$ implies $A \Rightarrow \left(\phi(x, \mathbf{y}) \iff x \in S\right)$.

\begin{figure}[h]
\begin{prooftree}
\AxiomC{$(S, A) \vdash \phi(x, \mathbf{y})$}
\AxiomC{$(S', A') \vdash \psi(x, \mathbf{y})$}
\BinaryInfC{$(S \sqcap S', A \cup A' \cup A_{S\sqcap S'}) \vdash \phi \land \psi (x, \mathbf{y})$}
\end{prooftree}
\caption{And}
\label{and}
\end{figure}

\begin{figure}[h]
\begin{prooftree}
\AxiomC{$(S, A) \vdash \phi(x, \mathbf{y})$}
\UnaryInfC{$(S^c, A) \vdash \lnot \phi(x, \mathbf{y})$}
\end{prooftree}
\caption{Not}
\label{not}
\end{figure}



\begin{figure}[h]
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$([y; +\infty), \emptyset) \vdash y \leq x$}
\end{prooftree}

\begin{prooftree}
\AxiomC{}
\UnaryInfC{$((-\infty; y), \emptyset) \vdash x < y$}
\end{prooftree}

\caption{Base Cases}
\label{basecases}

\end{figure}

Figures \ref{and}, \ref{not} and \ref{basecases} are the inference rules used to
compute an arithmetic domain and an associated set of assumptions for a given
formula.

Definition[Domains intersection, $S \sqcap S'$ and $A_{S \sqcap S'}$]:
If $S$ and $S'$ are two arithmetic domains associated to the assumptions $A$ and $A'$, then the intersection $S\sqcap S'$ is defined as an arithmetic domain such as\newline
$A \cup A' \cup A_{S\sqcap S'} \implies \left(\left(x \in S \land x \in S'\right)\iff x \in S \sqcap S'\right)$\newline (where $x \in S$ means $\left(\bigwedge\limits_{I\in S} x \in I\right)$).

Definition[Complementary Domains, $S^c$]:
If $S$ is an arithmetic domain, then $S^c$ is defined as a set of intervals such
as $\forall x.\ \left( \exists I \in S.\ x \in I\right) \iff \left( \not\exists I \in S^c.\ x \in I\right)$. 


Lemma[]:
If we can write a tree to derive $(S, A) \vdash \phi(x, \mathbf{y})$, then we have 
$A \Rightarrow \left(\phi(x, \mathbf{y}) \iff x \in S\right)$. Furthermore,
under the assumptions $A$, the intervals of S are disjoints:
\newline
if $[a, b) \in S$
and $[c, d) \in S$ then $A \implies \forall x\ \lnot \left( a \leq x \land x <
b\right) \lor \lnot \left( c \leq x \land x < d \right)$.

\begin{proof}
\end{proof}

## Interpret a constraint with a model

We are now interested in how we can write an algorithm which provides an arithmetic domain and a set of assumptions from a formula, following the inference rules of the former section.
Hence, the only two missing operations are building the domains $S^c$ and $S \sqcap S'$.
This algorithm must be correct, but we also want it to ensure several
properties, so as the resulting domains can then be used to compute the
cardinality at no further cost. These properties are on both the domain and the
assumptions associated to it.

This algorithm uses a model (i.e. an assignment of the free variables of the formula $F$ of equation \ref{maingoal} whose it is a model of), and computes
the arithmetic domain in respect to this model.


Property[Distincts]:
If $S$ is an arithmetic domain, and $A$ a set of assumptions then, if $I, J \in
S$ and $I \neq J$, $A \implies (x \in I \implies x \not\in J)$. Thus, $\{x\ |\ x \in
I\}$ and $\{x\ |\ x \in J\}$ are disjoints\footnote{Here, $x \in I$ is still defined as $a \le x \land x < b$ if $I = [a, b)$.}.


Property[Consistency]:
If $A$ is a set of assumptions, then it is consistent if the conjunction of
it elements is satisfiable.

If the property \ref{distincts} holds and every interval of $S$ is finite, then:

$A \implies \sharp\{ x \in S \} =
\sum\limits_{[a, b) \in S} b - a$.


#### Intersection
$S$ and $S'$ are both arithmetic domain, i.e. sets of symbolic intervals. Thus,
to do the intersection of the domains, we are going to do the intersection of
an interval $I$ of $S$ and an interval $J$ of $S'$. So, if $I = [a, b)$ and
$J = [c, d)$, we want a new interval $K_{I, J} = [e, f)$ such as $A \cup A' \cup
A_{S \sqcap S'} \implies \left(x \in I \land x \in J \iff x \in K_{I, J}\right)$.
Then, the intersection of the domains can be defined as $S \sqcap S' = \{ K_{I, J} \ |\ I \in S, J \in S'\}$.

Now, let's assume we have a model $\mathcal{M}$.
$x_\mathcal{M}$ is defined as the value of $x$ in this model, and more generally
for any term $t$ of theory $T_{\mathbb{Z}}$ (and $+\infty$, $-\infty$),
$t_{\mathcal{M}}$ is the interpretation of $t$ in this model.

In what follows, we describe a way to compte $K_{I, j}$ as well as $A_{S \sqcap
S'}$ in regards to the model, so as the assumptions are consistents (and the model
satifies them).

Let $I = [a, b) \in S$ and $J = [c, d) \in S'$, 
if $max(a_\mathcal{M}, c_\mathcal{M}) < min(b_\mathcal{M}, d_\mathcal{M})$,
then $K_{I, J} = [max(a, c), min(b, d))$ (where $max(a, c)$ is $a$ if $a_\mathcal{M} > c_\mathcal{M}$, else $c$), else it is undefined (because in the model, the interpretation of the intervals are indeed disjoints).

So, this is the intersection of $I$ and $J$ guided by the model. Every time
there is a decision to take (such as $a < c$), the values of the model are
looked at. Those decisions must be recorded, as they are the assumptions
required for this interpretation to be correct. The set $A_{S\sqcap S'}$ is
composed of those decision. It is clear that the model $\mathcal{M}$ satisfies
the set $A_{S \sqcap S'}$ (as well as $A$ and $A'$ by induction), thus $A_{S \sqcap S'} \cup A \cup A'$ is consistent, hence property \ref{consistency}.

It is also clear that by induction, if $S$ and $S'$ have the property \ref{distincts}, $S\sqcap S'$ also respect this property.

#### Negation

TODO


## Algorithm to solve arithmetic counting contraints

We describe an algorithm to solve a formula:
\begin{equation}
F(\mathbf{y}, c_1, …, c_n) \land
\bigwedge_{i = 1} ^n c_i = \sharp\{x\ |\ \phi_i(\mathbf{y}, c_1, …, c_n, x)\}
\end{equation}
where $F$ does not contain counting constraints.

We assume we have an SMT solver that can solve formulas written with the
theories $\mathbf{T}_\mathbb{Z}, \mathbf{T}_{eq}, \mathbf{T}_1, …, \mathbf{T}_m$. It needs to
support some operations (besides the variable definitions): `assert` (adds
a formula to the current context), `check-sat` (checks the satisfiability
of the conjunction of the formulas in the current context), `push` (creates a
new context with the current context formula), `pop` (restores the context to
the last `push` call). These operations are supported by most modern SMT solvers which can work in an incremental way.

\begin{algorithm}
\caption{Satisfiability of arithmetic formula with counting constraints}\label{arith}
\begin{algorithmic}[1]
%\Procedure{MyProcedure}{}
\State \Call{assert}{$F(\mathbf{y}, c_1, …, c_n)$}
\While{$\mathcal{M} = $ \Call{check-sat}{\ } }
	\State \Call{push}{\ }
	\State $A \gets \emptyset$
	\ForAll{ $i$ in $[1..n]$}
		\State $A_i, S_i \gets $ \Call{interpret-constraint}{$c_i$, $\phi_i$,
		$\mathcal{M}$}
		\State $A \gets A \cup A_i$
		\If{$S_i$ is infinite}
			\State \Call{assert}{$\lnot A$}
			\State \Call{continue}{}
		\EndIf
	\EndFor
	\State \Call{assert}{$A$}
	\State \textsc{assert}$\left(\bigwedge\limits_{i=1}^n c_i = \sum\limits_{[a, b] \in S_i} b - a\right)$
	\If {\Call{check-sat}{\ } }
		\State \Call{pop}{\ }
		\State \Return{sat}
	\EndIf
	\State \Call{pop}{\ }
	\State \Call{assert}{$\lnot A$}
\EndWhile
\State \Return{unsat}
\end{algorithmic}
\label{arith}
\end{algorithm}

The algorithm \ref{arith} works as follows: it asks for a model $\mathcal{M}$ of the formula
$F$, then interpret every counting constraints to a symbolic expression under some
assumptions. The equality between those expressions and the $c_i$, as well as the
assumptions are then enforced with an `assert`. Then, if the solver says it is satisfiable, the values of the $c_i$ in the new model respect the counting constraints equations.
If it is not, then it means that the assumptions $A$ and the counting
constraints equations are not consistent, thus $\lnot A$ can be asserted, and we
can re-try.

Lemma[Termination]:
Algorithm \ref{arith} terminates.

\begin{proof}
In the former section, we explained how the assumptions set was computed. An
assumption can be an equality, a disequality or an inequality between two terms
that appear in the formulas $\phi_i$. Thus, there is a finite number of possible
set of assumptions.

At every iteration, there is a $\text{\textsc{assert}}(\lnot A)$, hence the fact that there is
a finite number of iterations.
\end{proof}

Lemma[Correctness]:

\begin{proof}TODO\end{proof}

#### Example

TODO

# Solving Counting Constraints with Arrays

In this section, we describe an extension of the previous algorithm to deal with
arrays.
The syntax for $k$ arrays $a_1, …, a_k$ is described in Figure \ref{syntaxarray}. It is important to note
that arrays are only accessed on the quantified variable, and not on a general
term built on this variable (such as $x + 1$, or a nested array rerad). Removing this syntax restriction
leads to an undecidable array theory fragment, as stated in @bradley2006s, even
for small additions to the fragment.

An array has a size, which is an arithmetic variable of the theory
$\mathbf{T}_\mathcal{Z}$. This is similar to @AlbertiGP16 (with the subtle
difference that different arrays can have different size) but unlike @ConchonGKMZ12, whose fragment does not provide a syntax to express array length. In the context of fault tolerant systems, this is an important detail, as we typically want to specify that a fraction of the systems can be faulty.

As soon as there is an array term in the counting constraints, the cardinality can no longer be infinite, as the array can only be accessed on a finite interval.

It may be interesting to have array reads outside of the counting
constraints, but they can be rewritten as counting constraints, like in
@bradley2006s or @AlbertiGP16. In the next section we explain how this algorithm can be changed to work with the usual arrays of an SMT solver.

\begin{figure}[h]
\begin{grammar}
	
<counting constraints> $\psi(x)$ ::= $\psi(x)$ $\land$ $\psi(x)$
\alt $\psi(x)$ $\lor$ $\psi(x)$
\alt $\lnot$ $\psi(x)$
\alt <atoms> of $\mathbf{T}_i$ where $x$ does not appear
\alt $x \leq y$ where $y$ is a variable of $\mathbf{T}_\mathbb{Z}$
\alt $y \textless x$ where $y$ is a variable of $\mathbf{T}_\mathbb{Z}$
\alt $\phi(a_1[x], …, a_k[x])$ where $\phi$ does not have counting constraints


\end{grammar}
\caption{Array Extension}
\label{syntaxarray}
\end{figure}


## Algorithm

The algorithm to solve counting constraints with arrays is mostly the same as
algorithm \ref{arith}, the main difference is that the constraints on the arrays must be
saved and then be consistent.

During my internship, I experimented several possible algorithms to manipulate
those constraints. The algorithm I describe here migth seem a bit brutal as it
extensively rely on the underlying SMT solver, but it worked better than the
other attempts, probably because a modern SMT solver can be much more efficient
than a less optimized specialized algorithm.

### Arithmetic And Arrays Domains

Definition[Array Constraint]:
An array constraint is a first order, quantifier free, formula whose free variables are the free variables of the formula
and the variables $a_1[\cdot], …, a_k[\cdot]$.

Definition[Domain]:
An domain is a finite set of symbolic intervals (definition
\ref{symbolic}), every one of them associated to an array constraint (definition
\ref{array}).

An arithmetic domain (definition \ref{arithmetic}) can then be seen as a domain
whose every symbolic interval is associated to the constraint `true`.

Figure \ref{arraybases} introduces the rules  for the base cases of domain computations. The conjonction and the negation are still done according to the rules \ref{not} and \ref{and}.

\begin{figure}[h]
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$((-\infty, +\infty), \phi(a_1[x], …, a_k[x])), \emptyset \vdash \phi(a_1[x], …, a_k[x])$}
\end{prooftree}
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$([y; +\infty), \top), \emptyset \vdash y \leq x$}
\end{prooftree}

\begin{prooftree}
\AxiomC{}
\UnaryInfC{$((-\infty; y), \top), \emptyset \vdash x < y$}
\end{prooftree}

\caption{Base Cases}
\label{arraybases}
\end{figure}

So, we need to redefine the operations of intersection ($S \sqcap S'$) and negation ($S^c$) for those domains.

### Intersection and negation of the domains

Let $S$ and $S'$ two domains. The intersection is done the same way it is done for arithmetic domains, but when intersecting two symbolic intervals, if the resulting intervals is not empty, then we associate to the result the conjonction of the two array constraints.

### Enforcing the Domains

We now want to generate a set of constraints that are equivalent to the satisfiability of the formula and the counting constraints.

We start from a set of $l$ domains (one for every counting constraints) and generate a set of arithmetic constraints.

#### Slice

The first operation we do is what we call _slicing_. It means that the domains must be transformed so as they all have the same intervals. In practice, we are looking for a subdivision of $[A, B)$ (where $A$ is the lower bound of every array index and $B$ the upper bound) which can be used to express every domains.
This is a simple operation that I do not detail here, intuitively every bound of the intervals is collected, then they are split into equality classes and ordered (in the meantime the set of assumptions may be made bigger).

#### Partition

At this point we have a set of domains who all have the same intervals but different array constraints associated to them. For an interval $I$, we consider every constraints associated to it, i.e. $\phi_1, …, \phi_l$. From these one we can create a set of formula $\psi_1, …, \psi_{l'}$ which are a partition\footnote{A partition is a set of formula $\psi_1, …, \psi_n$ such as $\psi_1 \lor … \lor \psi_n \equiv \top$ but $\forall i, j. \; \psi_i \land \psi_j \equiv \bot$.}. There can be at most $2^l$ formula, but of course that can be dramatically reduced in practice with heuristics such as memoization are inclusion detection.

#### Arithmetic Constraints

$I = [a, b)$ is supposed to be a finite interval (or it means that the array is accessed on an infinite intervals, which is not supposed to happen), so, it has a length $b - a$. As $\psi_1, …, \psi_{l'}$ is a partition, it holds that $b - a = \sum\limits_{i = 1}^{l'} \sharp\{x \ |\ \psi_i(a_1[x], …, a_n[x])\}$.We create a new variable $v_i$ (such as $0 \le v_i$) for every $\sharp\{x\ |\ \psi_i(a_1[x], …, a_n[x]\}$ and adds the constraint $b - a = \sum v_i$ to the solver. As long as every $\psi_i$ is satisfiable, then we can build arrays that satisfy $v_i = \sharp\{x\ |\ \psi_i(a_1[x], …, a_n[x]\}$. Hence, we must add $v_i > 0 \implies \psi_i(a_{i, 1}, …, a_{i, n})$ (with new variables $a_{i, 1}, …$.


#### Algorithm

See algorithm \ref{arrayalgo}.

\begin{algorithm}[h]
\caption{Satisfiability of arithmetic and formula with counting constraints}\label{arith}
\begin{algorithmic}[1]
%\Procedure{MyProcedure}{}
\State \Call{assert}{$F(\mathbf{y}, c_1, …, c_n)$}
\While{$\mathcal{M} = $ \Call{check-sat}{\ } }
	\State \Call{push}{\ }
	\State $A \gets \emptyset$
	\ForAll{ $i$ in $[1..n]$}
		\State $A_i, S_i \gets $ \Call{interpret-constraint}{$c_i$, $\phi_i$,
		$\mathcal{M}$}
		\State $A \gets A \cup A_i$
		\If{$S_i$ is infinite}
			\State \Call{assert}{$\lnot \left( A \right)$}
			\State \Call{continue}{}
		\EndIf
	\EndFor
	\State \Call{slice}{$(S_i)_i$}
	\State \Call{partition}{$(S_i)_i$}
	\State \Call{assert}{$A$}
	\State \Comment{$v_\alpha$ is a variable corresponding to $phi_\alpha$, that $c_i$ selects}
	\State \Call{assert}{$\bigwedge\limits_{i=1}^n c_i = \sum\limits_{[a, b] \in S_i} \sum\limits_{\alpha} v_{\alpha}$}
	\State \Call{assert-constraints}{$(S_i)_i$}
	\If {\Call{check-sat}{\ } }
		\State \Call{pop}{\ }
		\State \Return{sat}
	\EndIf
	\State \Call{pop}{\ }
	\State \Call{assert}{$\lnot \left( A \right)$}
\EndWhile
\State \Return{unsat}
\end{algorithmic}
\label{arrayalgo}
\end{algorithm}

#### Example

TODO

# Arrays

The previous algorithm transforms every array reads and write into an array
constraint. This is not very efficient, because the underlying SMT solver has no
clue regarding the consistency of the values it provides for an array read.
That's why it is interesting to change this algorithm to make it work with a
usual array theory of an SMT solver. The algorithm then has to take into account the decision that the SMT solver when it outputs the constraints, so as the result is consistent (i.e. the arrays are not defined twice).

Unfortunately, as our algorithm operates outside of the solver, the interactions
they can have are quite limited. Thus, it is important to understand how the
theory of arrays is usually implemented to make it work with the counting
constraints algorithm described in the last section.

## The theory of arrays implemented in most SMT solvers

A state of the art implementation of the theory of arrays is described in @de2009generalized. More specifically, it explains how works the SMT solver Z3.

The only two operations on arrays are `select` and `store`. `(select a x)` access the array $a$ at index $x$ (also written $a[x]$), while
`(store a x b)` creates a new array whose elements are the same as $a$ but for
$x$, where it is set to $b$. The two axioms of this theory are:

\begin{subequations}
	\begin{align}
		\forall a:(\sigma \implies \tau), i:\sigma, v:\tau\, .\, store(a, i, v)[i] = v
		\\
		\forall a:(\sigma \implies \tau), i:\sigma, j:\sigma\, .\, i \neq j \implies store(a, i, v)[j] = a[j]
	\end{align}


	Additionnaly, there is the extensionnality axiom:

	\begin{align}
		\forall a:(\sigma \implies \tau), b:(\sigma \implies \tau)\, .\, a \neq b \iff \exists i\: a[i] \implies a[i] \neq b[i]
	\end{align}
\end{subequations}

For the first two axioms, it is clear that the SMT solver is only going to take decisions about terms index which appear inside a `store` and a `select`.
An equality might introduce additional indexes to make two arrays different. That's why an array extracted from a model of an SMT solver always follows the same pattern: special values are defined for a finite number of terms (an over-approximation of those terms can be obtained by looking at the formula), and then a default value. And the default value does not matter, as long as there is no equality.


## Using an off-the-shelf SMT solver for arrays

Thus, to ensure the consistency of the counting constraint algorithm and the SMT solver decisions about arrays, we only have to take into account the value at those index terms, and array equality if needed.

The first problem can be solved by tracking those index terms, then looking at the model which slice they belong to, and group them by slice. Then, for every array constraint $\phi_\alpha$ of this slice, some new clauses must be sent to the solver to ensure the consistency of this values decided by the SMT solver with the number of $x$ which satisfies $\phi_\alpha$

The equality between two arrays must also be tracked, they must be taken into account when the arithmetic constraints are expressed at the end of the algorithm by adding new array constraints. Some heuristics (such as substitution of the arrays when there is equality) can also be used.

# DPLL(T)

## Introduction

TODO

## Integration with a general purpose DPLL based SMT solver

Our algorithm works by assuming a set of assumptions and checking that cardinality values that they imply is consistent. The worst case for the assumptions is to be a total ordering over every integer variable and an assumptions on every atom of the formula. The number of total ordering over $n$ variables is $n!$\footnote{More than that when the case where two variables are equal is taken into account.}, which makes the algorithm unpractical if there is not enough constraints on those variables in the formula.

That is why it would be interesting to have a better explanation of why it is not `sat` and not only learn that the formula is `unsat` with this particular ordering. That requires an explanation from the SMT solver and a better integration with both the arithmetic theory and the arrays theory.

Furthermore, partial assumptions are sufficient to compute the bounds of a cardinality, and may also be sufficient to detect an inconsistency earlier in the solving of the formula, hence avoiding useless computations. Some work for abstract sets has already be done in this direction @cardinalityset.

The way the algorithm works is not very different from the way a theory is usually modeled in DPLL(T) based solver, the main differences being that it has nested formula and has to interact with the array and arithmetic theories. So, adapting it to be just another theory in a solver may be worthwhile.

\newpage

# Conclusion {-}

# References
