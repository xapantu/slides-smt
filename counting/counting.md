---
title: Solving Counting Constraints on Arithmetic in SMT
date: August 28, 2016
header-includes:
  - \usepackage{tikz}
  - \usepackage{bussproofs}
toc: true
---

# Introduction

- @AlbertiGP16

# DPLL(T)

formalisation de dpll, particulièrement la partie des littéraux, etc

# Constraints Interpretation

We call assumptions a set $A$ whose elements are atoms (boolean variable or arithmetic atom). In a first order formula, writing $A$ means the conjuctions of the atoms of $A$.

We write $(S, A) \vdash \phi(Z, x)$ to say that $A \Rightarrow (\phi(Z,\mathbf{x}) \iff Z \in S)$.

Thus, it holds that $A \Rightarrow (\# \{ Z \ | \ \phi(Z, x) \} = \#S)$.



\begin{figure}[h]
\begin{prooftree}
\AxiomC{$(S, A) \vdash \phi(Z, \mathbf{x})$}
\AxiomC{$(S', A') \vdash \psi(Z, \mathbf{x})$}
\BinaryInfC{$(S \sqcap S', A \cup A' \cup A_{S\sqcap S'}) \vdash \phi \land \psi (Z, \mathbf{x})$}
\end{prooftree}
\caption{And}
\end{figure}

\begin{figure}[h]
\begin{prooftree}
\AxiomC{$(S, A) \vdash \phi(Z, \mathbf{x})$}
\UnaryInfC{$(S^c, A) \vdash \lnot \phi(Z, \mathbf{x})$}
\end{prooftree}
\caption{Not}
\end{figure}



\begin{figure}[h]
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$([x; +\infty), \emptyset) \vdash x \leq Z$}
\end{prooftree}

\begin{prooftree}
\AxiomC{}
\UnaryInfC{$((-\infty; y), \emptyset) \vdash Z < y$}
\end{prooftree}

\caption{Base Cases (Z is the quantified variable)}
\end{figure}

# Arrays

## The theory of arrays

## Cubes from Constraints

## `select` and `store` with counting contraints

## Using an off-the-shelf SMT solver for arrays

# Integration with a general purpose DPLL based SMT solver

# Generalization for free

# Bibliography
