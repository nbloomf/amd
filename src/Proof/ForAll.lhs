---
title: For All
---

Equality is the first kind of judgement that allows reasoning about expressions; the other is _universal quantification_. If $P$ is a judgement, and $x$ an expression variable, then $$\forall x . P$$ is a judgement, representing the statement _for all $x$, we have $P$_. The introduction and elimination rules for $\forall$ are a little different from our other rules because they involve _side conditions_.

The $\forall$-introduction rule looks like this:

$$\begin{array}{c}
P[w \mapsto a] \\ \hline
\forall x . P[w \mapsto x]
\end{array}$$

where [square brackets] again represent a metasyntactic substitution. This proof tree is only valid if it satisfies the following extra condition: the variable $a$ cannot be free in any assumption or hypothesis on which the proof of $P[w \mapsto a]$ depends. In a sense, free variables in a judgement are universally quantified over the whole proof, and the $\forall$-introduction rule lets us turn this into a universal quantification over a single judgement.

The $\forall$-elimination rule looks like this:

$$\begin{array}{c}
\forall x . P[w \mapsto x] \\ \hline
P[w \mapsto a]
\end{array}$$

Both of these rules are special cases in the proof checker because they require special syntax; we need to specify the variable quantified over and the substitution image. Lets see an example.

~~~ {.mycelium}
theorem forall-conj-1
if
  * P /\ (∀x.Q)
then
  * ∀x. P /\ Q

proof
1. P /\ (∀x.Q) : assumption 1
2. P : use conj-elim-l; 1
3. ∀x.Q : use conj-elim-r; 1
4. Q : forall-elim x -> y; 3
5. P /\ Q : use conj-intro; 2, 4
6. ∀x. P /\ Q : forall-intro y -> x; 5
~~~

This example is not great, because the statements inside of $\forall$ have no expression variables at all. We'll see better examples later.
