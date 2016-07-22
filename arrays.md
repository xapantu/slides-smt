---
header-includes:
  - \usepackage{tikz}
---
# Solving arrays constraints

First, we assume that we only try to solve a set of counting constraints on arrays. Further optimizations are discussed later.

Let $A$ be the type on array indices (typically an interval on $\mathbb{N}$), and let $a_1$, $a_2$, …, $a_n$ be arrays from $A$ to $bool$.

A counting constraints is a formula such as $\#\{x\ |\ \Phi(a_1[x], …, a_n[x])\} = a$ where $\Phi$ is a first order formula, and $a$ a variable which is a natural number.

## Constraints tree

A first approach to solve (rather inefficiently) those constraints is to build
recursively a tree and deduce a set of arithmetic constraints from it. An array
variable is associated to every inner node of the tree. The left tree of
every inner node if a subtree handling the case when the variable is false, the
right tree is for the case when the variable is true. For every
constraints, a selection state is associated to every leaves of this tree. A
selection state is a member of the enum `Selected | Unselected |
No_constraints`.

Now, let $\Phi_1$, $\Phi_2$, …, $\Phi_n$ be the formula in every counting constraints that we want to solve.

This tree is built in a lazy way by browsing the $\Phi_i$.

The tree is always kept, it can only kept and the leaves can be reset to
No_constraints.

~~~python
select_leaves(tree, phi):
  if phi == "a[x] = true":
    if a in tree[i]:
	  unselect all leaves left to the nodes corresponding to the variable a;
	  select all leaves right to the nodes corresponding to the variable a,
	  which are in a No_constraints state;
	else:
	  add a node variable in place of every Selected leaves;
	  select_leaves(tree, phi)
  else if phi == "l /\ m":
    select_leaves(tree, l); select_leaves (tree, m);
  else if phi == "not l":
    for every leaves of tree, switch Selected to Unselected and Unselected to
	Selected

tree[0] <- empty;
for i in [1..n]:
  tree[i] <- reset tree[i-1];
  select_leaves(tree[i], phi(i));
~~~

## Constraints tree to arithmetic constraints

The last tree built is the biggest one. One variable of type `Int` is created
for every node (including the leaves), and every inner node is set to be the sum
of it two children. Now, we can replace every $\#\{x\ | \Phi_i(…) \}$ by the sum
of the variable of both the `No_constraints` and `Selected` leaves.

On top of that, the sum of every leaf is equal to the size of the array.


## Example

Let a, b be arrays whose index type is $A = [1..N]$.

- $\#\{x\ |\ a[x] \land b[x] \} = 2*N/3$
- $\#\{x\ |\ a[x] \land \lnot b[x] \} = 2*N/3$

The tree for the first formula is
\begin{tikzpicture}[level/.style={sibling distance = 5cm/#1,
  level distance = 0.7cm}]
\node {a}
    child { node {b}
		child { node { Unselected } }
		child { node { Unselected } }
	}
    child { node {b}
		child { node { Unselected } }
		child { node { Selected } }
	}
		;
\end{tikzpicture}

The second one is :

\begin{tikzpicture}[level/.style={sibling distance = 5cm/#1,
  level distance = 0.7cm}]
\node {a}
    child { node {b}
		child { node { Unselected } }
		child { node { Unselected } }
	}
    child { node {b}
		child { node { Selected } }
		child { node { Unselected } }
	}
		;
\end{tikzpicture}


# Optimizing some operations

## Store

## Select

## Non extensional equality

## Detecting implications

## Equality to a constant arrays

## Equality
