---
title: Model Checking of Fault-tolerant Systems
author: Lucas Baudin
date: June 15, 2016
theme: "Warsaw"
toc: true
header-includes:
 - \usepackage{mathtools}
---


# Model Checking Modulo Theories

## Model Checking

- a state type is a list of variables: $\mathbf{x}$
- a state is a valuation for these variables
- a transition is a formula over the current state variables and the next state variables \newline
(usually represented as a guard $H(\mathbf{x})$ and a (partial) assignment $V(\mathbf{x'})$)
- $(H_1(\mathbf{x}) \land V _1 (\mathbf{x'})) \lor … \lor (H_n(\mathbf{x})\land V_n(\mathbf{x'}))$

## Modulo Theories

- the formulae can be in any theory
- example:
	 - if the state type is a variable $x$ of type int
 	 - transition: $x < 0 \land x' = x \lor x \ge 0 \land x' = x + 1$
 	 - describes a system which has a variable $x$ which keeps increasing unless is is lower than $0$.

# Model Checking of a Fault-tolerant System

## The Byzantine General Problem

## Pseudo-Code

# Sally


## A model checker for infinite-state systems

- [sri-csl.github.io/sally](http://sri-csl.github.io/sally/)
- a symbolic model checker
- several engines: bmc, kind, ic3
- works with various smt solvers: mathsat, yices2, z3

## Input language

- lisp-like language
- low level
- easy to parse and work with

## Input language

- state type
```
(define-state-type my_state_type 
  ((x Real) (y Real))
)
```
. . .

- state formula
```
(define-states x_is_zero my_state_type
  (= x 0)
)
```

## Input language

- transition: a first order formula over state variables and next state variables
```
(define-transition my_transition my_state_type
  (or
    (= next.x (+ state.x 1))
    next.x_is_zero
  )
)
```

## Input language

- queries


# A new old input language: Sal

## Sal

- an older model checker, developed at SRI
- developed actively until 2006, minor versions until 2013
- finite state systems

## Input language

- already used
- supports modules, composition

## Input language

[columns]

[column=0.5]

~~~ocaml

my_module: MODULE
BEGIN
  OUTPUT
  	x: REAL,
  	y: REAL
  INITIALIZATION
  	x = 0;
  TRANSITION
    ...
END;

~~~

[column=0.5]

~~~ocaml
TRANSITION
  [x >= 0 -->
     x' = x + 1;
	 y' IN { i: REAL | TRUE }
  []
   TRUE -->
     x' = 0;
  	 y' IN { i: REAL | TRUE }
  ]
~~~

[/columns]

## Input language

[columns]

[column=0.35]

- a lemma is translated to a Sally query
- multiple lemma
- syntax for temporal logic (not available in Sally)

[column=0.65]

~~~ocaml
my_context: CONTEXT =
BEGIN
  my_module: MODULE
       ...
  
  always_positive: LEMMA
    my_module |- G(x >= 0);

  wrong_lemma: LEMMA
    my_module |- G(x > 0 -> x = 1)

END

~~~

[/columns]


# Parametrization

## Arrays

## Quantifiers

- for most examples, they can be avoided in transitions
- works only with z3
- example:

~~~
(forall (i Int) (select a i))
~~~

## Counting in SMT

- $\phi(y) \land y = \#\left\{ x | \psi(x) \right\}$
- $\psi(.)$: first order formula of Presburger arithmetic, then with arrays too
- how is it solved?


## State of the art

- @bradley2006s: a decision procedure for a fragment of arrays, with distinct theories for elements and indexes 
- @AlbertiGP16: a decision procedure for counting on arithmetic and arrays, via various rewriting and quantifier eliminations, mix index and elements theories, but quantify only over one element at a time
- @bjornercardinalities: a model checking oriented way to deal with arrays (one update at a time for every arrays)

## Counting over Presburger arithmetic

- given a model, one can compute the value of $\#\left\{ x | \psi(x) \right\}$
- given an ordering on the integer variables, one can compute the symbolic value of $\#\left\{ x | \psi(x) \right\}$

- $\Rightarrow$ symbolic computation of cardinalities, for the ordering of a given model

## Counting over Presburger arithmetic, with an ordering

- the ordering is called an oracle: when asked wether $a > b$, it looks in the model the value of $a$ and $b$ and answers accordingly.
- when the cardinality is computed symbolically, it is equal to a formula which holds under some assumptions, and the oracle can say what they are

. . .

- example: $y = \#\{ x | 0 \leq x < z \land 0 \leq x < u\}$

- if the oracle says $z > u$, then $y$ can be computed and $y = z$.
- under the assumption $z > u$, $y = z$

## Counting over Presburger arithmetic, with an ordering

- compute a symbolic interval list in which the formula is satisfiable
  i.e. $\exists I \in V_x(\psi) \ x \in I \Leftrightarrow \psi(x)$


- if members of $V_x(\psi)$ are disjoint \
  $card(V_x(\psi)) = \sum_{[v, v'] \in \#_x(\psi))} (v - v') = \# \{ x | \psi(x)\}$

. . .

- $V_x(y < x ) = \{[y, +\infty)\}$

## Counting over Presburger arithmetic, with an ordering

- $V_x(\psi \land \phi ) = V_x(\psi) \sqcap V_x(\phi)$ \newline
  where $A \sqcap B$ is the set of every intersection of an interval of A with an interval of B (of course some are empty and must be deleted)

. . .

- Intersection between two intervals: $[a, b)$ and $[c, d)$ can be computed: there is an oracle giving the ordering on the variables, so $max(a, c)$ and $min(b, d)$ are computable given the assumptions that the oracle makes.
  \newline
  Then the intersection is $[max(a, c), min(b, d))$ if $max(a, c) \leq min(b,d)$


## Counting over Presburger arithmetic, with an ordering

- if $V_x(\psi) = \{ [a_1, b_1), … [a_n, b_n) \}$ (with $a_1 \leq b_1 \leq … \leq b_n$, $a_1 \neq -\infty$ and $b_n = + \infty$)
- $V_x(\lnot \psi) = \{ (- \infty, a_1), [b_1, a_2), …,  [b_n, +\infty) \}$
- other cases are easy too, disjunction on $a_1 = -\infty$ and $b_n = +\infty$

## Counting with multiplication

- to deal with constant multiplications, a modulo information can be added to every intervals (such as $([5, 10), = 1 [3])$ are the integers $x$ between 5 and 10 and such that $3 | x - 1$)
- intersection, negation of these intervals can be done in an analog way

## Future Work

- Counting over arrays
- IC3 with arrays and counting quantifiers

## References
