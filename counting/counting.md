---
title: Solving Counting Constraints on First Order Formulas in SMT
date: August 28, 2016
header-includes:
  - \usepackage{tikz}
  - \usepackage{bussproofs}
  - \usepackage{syntax}
  - \usepackage{amsthm}
numbersections: true
subparagraph: true
---
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}
\newtheorem{property}{Property}

# Introduction {-}

# Model Checking of parametrized and fault tolerant systems

## Counting Contraints

Interesting because provides a restricted way to quantify, weaker than both
existential and universal quantifications, but easier to solve. @ge2009complete

# Solving Counting Constraints for arithmetic

## Syntax

We consider a set of distinct theories $\mathbf{T}_\mathbb{Z}$,
$\mathbf{T}_{eq}$,
$\mathbf{T}_2$, …, $\mathbf{T}_n$, where $\mathbf{T}_\mathbb{Z}$ is the theory
of $\mathbb{Z}$
Atoms and variables of these theories are defined as usual. We work with
formulas that are built with the syntax of \ref{grammar}. The terms of the form
$c = \sharp\{ x\ |\ \psi(x) \}$ are called counting constraints. Here,
$\sharp\{ x\ |\ \psi(x)\}$ denotes the cardinality of a set $S$ such as
$x \in S \iff \psi(x)$.

\begin{figure}[h]
\label{grammar}
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

We consider a subclass of formula built on the syntax of Figure \ref{formula}, formulas of the form:

$F(c_1, …, c_n, \mathbf{y}) \land \bigwedge\limits_{i=1}^n c_i = \sharp\{ x \ |\ \psi_i(x, c_1, …, c_n,
\mathbf{y})\}$

where no counting constraints appear in $F$.

We are going to explain a way to decide this formula, i.e. saying wether they
are satisfiable, and if yes give a model that satisfies this formula.

We assume that we already have a solver to solve formula without counting
constraints (which can give a model if the formula is `sat`).

In @AlbertiGP16 and @schweikardt, there is already a way to solve those formula.
However, while they definitively explain that the problem is decidable and why, they heavily rely on quantifier elimination and thus may not be very practical.

## Constraints Interpretation

\begin{definition}[Assumptions]
\label{assumptions}
We call assumptions a set $A$ whose elements are atoms of the theories $\mathbf{T}_i$. In the context of a first order formula, writing $A$ means the conjuctions of the atoms of $A$.
\end{definition}

\begin{definition}[Symbolic Interval]
\label{interval}

A symbolic interval is a couple of values that are either arithmetic variables,
constants or $\infty$.
If $I = [a, b)$, $x \in I$ is defined as $x < b \land a \le x$.

It is said to be finite if none of the bounds are infinite.
\end{definition}

\begin{definition}[Arithmetic Domain]
An arithmetic domain is a finite set of symbolic intervals (definition
\ref{interval}). It is usually associated to
some assumptions (definition \ref{assumptions}) which make them disjoint and
ensure that the lower bound of an interval is actually lower than the upper
bound.

\end{definition}

If S is an arithmetic domain, we abusively write $x \in S$ for $\left(\bigvee\limits_{I \in S} x \in I\right)$.
We are going to prove that $(S, A) \vdash \phi(x, \mathbf{y})$ implies $A \Rightarrow \left(\phi(x, \mathbf{y}) \iff x \in S\right)$.

%%Thus, it holds that $A \Rightarrow \left(\sharp \{ x \ | \ \phi(x, \mathbf{y}) \} = \sharp \left( \cup_{I \in S} I\right)\right)$.



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

\begin{definition}[Domains intersection, $S \sqcap S'$ and $A_{S \sqcap S'}$]

\end{definition}

\begin{definition}[Complementary Domains, $S^c$]

If $S$ is an arithmetic domain, then $S^c$ is defined as a set of intervals such
as $\forall x.\ \left( \exists I \in S.\ x \in I\right) \iff \left( \not\exists I \in S^c.\ x \in I\right)$. 

\end{definition}


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

\begin{lemma}

\end{lemma}

## Interpret a constraint with a model

We are now interested in how we can write an algorithm which provides an arithmetic domain and a set of assumptions from a formula, following the inference rules of the former section.
Hence, the only two operations which are not trivial are building the domains $S^c$ and $S \sqcap S'$.
This algorithm must be correct, but we also want it to ensure several
properties, so as the resulting domains can then be used to compute the
cardinality at no further cost. These properties are on both the domain and the
assumptions associated to it.


Property[Distincts]:
If $S$ is an arithmetic domain, and $A$ a set of assumptions then, if $I, J \in
S$ and $I \neq J$, $A \implies (x \in I \implies x \not\in J)$. Thus, $\{x\ |\ x \in
I\}$ and $\{x\ |\ x \in J\}$ are disjoints.


Property[Consistency]:
If $A$ is a set of assumptions, then it is consistent if the conjunction of
it elements is satisfiable.

If the property \ref{distincts} holds and every interval of $S$ is finite, then:

$A \implies \sharp\{ x \in S \} =
\sum\limits_{[a, b) \in S} b - a$.


Lemma[Correctness]:


## Algorithm

\begin{figure}

\end{figure}


Lemma[Termination]:

Lemma[Correctnes]:

# Solving Counting Constraints With Arrays

## Syntax

## Algorithm

# Arrays

@de2009generalized

## The theory of arrays implemented in most SMT solvers

## `select` and `store` with counting contraints

## Using an off-the-shelf SMT solver for arrays

# DPLL(T)

## Basic Principles

formalisation de dpll, particulièrement la partie des littéraux, etc

## Integration with a general purpose DPLL based SMT solver

# Generalization

# References
