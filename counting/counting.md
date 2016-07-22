---
title: Solving Counting Constraints on Arithmetic in SMT
header-includes:
  - \usepackage{tikz}
  - \usepackage{bussproofs}
---

# Introduction

# DPLL(T)

formalisation de dpll, particulièrement la partie des littéraux, etc

# Constraints Interpretation

règles d'inférence

\begin{figure}[h]
\begin{prooftree}
\AxiomC{$(S, A): \phi$}
\AxiomC{$(S', A'): \psi$}
\BinaryInfC{$(S \sqcap S', A \cup A' \cup A_{S\sqcap S'}): \phi \land \psi$}
\end{prooftree}
\caption{And}
\end{figure}


\begin{figure}[h]
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$([x; +\infty), \emptyset): x \leq Z$}
\end{prooftree}

\begin{prooftree}
\AxiomC{}
\UnaryInfC{$((-\infty; y), \emptyset): Z < y$}
\end{prooftree}

\caption{Base Cases (Z is the quantified variable)}
\end{figure}

# Generalization for free
