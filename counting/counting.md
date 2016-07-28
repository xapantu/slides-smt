---
title: Solving Counting Constraints on First Order Formulas in SMT
date: August 28, 2016
header-includes:
  - \usepackage{tikz}
  - \usepackage{bussproofs}
  - \usepackage{syntax}
  - \usepackage{amsthm}
toc: true
subparagraph: true
---
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}

\newpage

# Introduction

# Formulas

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
\end{figure}

Using some trivial rewriting, every formula built on the syntax of Figure 1 can
be shown to be equivalent to a formula such as:

$F(c_1, …, c_n, \mathbf{y}) \land \bigwedge\limits_{i=1}^n c_i = \sharp\{ x \ |\ \psi_i(x, c_1, …, c_n,
\mathbf{y})\}$

where $F$ is not built using any counting constraints.

We are going to explain a way to decide this formula, i.e. saying wether they
are satisfiable, and if yes give a model that satisfies this formula.

We assume that we already have a solver to solve formula without counting
constraints (which can give a model if the formula is `sat`).

In @AlbertiGP16 and @schweikardt, there is already a way to solve those formula.
However, while they definitively explain that the problem is decidable and why, they heavily rely on quantifier elimination and thus may not be very practical.

# Constraints Interpretation

\begin{definition}[Assumptions]
\label{assumptions}
We call assumptions a set $A$ whose elements are atoms of the theories $\mathbf{T}_i$. In a first order formula, writing $A$ means the conjuctions of the atoms of $A$.
\end{definition}

\begin{definition}[Symbolic Interval]
\label{interval}

A symbolic interval is a couple of values that are either arithmetic variables,
constants or $\infty$.
If $I = [a, b)$, $x \in I$ is defined as $x < b \land a \le x$.
\end{definition}

\begin{definition}[Arithmetic Domain]
An arithmetic domain is a set of symbolic intervals (definition
\ref{interval}). It is usually associated to
some assumptions (definition \ref{assumptions}) which make them disjoint and
ensure that the lower bound of an interval is actually lower than the upper
bound.

If S is an arithmetic domain, we abusively write $x \in S \iff \exists I \in S\ x
\in I$.
\end{definition}


We write $(S, A) \vdash \phi(x, \mathbf{y})$ to describe that $A \Rightarrow \left(\phi(x, \mathbf{y}) \iff x \in S\right)$.

Thus, it holds that $A \Rightarrow \left(\sharp \{ x \ | \ \phi(x, \mathbf{y}) \} = \sharp \left( \cup_{I \in S} I\right)\right)$.



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

\begin{definition}[Domains intersection, $S \sqcap S'$]

\end{definition}

\begin{lemma}
If we can write a tree to derive $(S, A) \vdash \phi(x, \mathbf{y})$, then we have 
$A \Rightarrow \left(\phi(x, \mathbf{y}) \iff x \in S\right)$. Furthermore,
under the assumptions $A$, the intervals of S are disjoints:

if $[a, b) \in S$
and $[c, d) \in S$ then $A \implies \forall x\ \lnot \left( a \leq x \land x <
b\right) \lor \lnot \left( c \leq x \land x < d \right)$.
\end{lemma}

\begin{proof}
\end{proof}


# Arrays

## The theory of arrays

## Cubes from Constraints

## `select` and `store` with counting contraints

## Using an off-the-shelf SMT solver for arrays

# DPLL(T)

formalisation de dpll, particulièrement la partie des littéraux, etc

# Integration with a general purpose DPLL based SMT solver

# Generalization

# Bibliography
