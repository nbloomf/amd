---
title: Equality
---

The inference rules we've seen so far for dealing with conjunction, disjunction, and implication all operate on judgements. But as it happens, we've got some extra simple judgements for dealing with "values". To be precise, the _values_ our logic knows about are just simply typed lambda expressions. We'll talk more about lambda expressions later. For now all we need to do is see how we can manipulate them in logic. There are three ways, and the first -- _equality_ -- is the subject of this page.

If $x$ and $y$ are lambda expressions, then $x = y$ is the simple judgement asserting that $x$ and $y$ are equal. We take equality of lambda expressions to be an undefined concept governed precisely by its inference rules.

The $=$-intro rule is simple enough to state: every lambda expression is equal to itself, and this does not require evidence. Lower case latin characters like $x$ will always represent expression variables.

$$\begin{array}{c}
       \\ \hline
 x = x
\end{array}$$

This rule is called `eq-intro`. It can be defined in the proof checker syntax, but is one of our special built-in forms for reasons we'll see in a bit.

The $=$-elimination rule, `eq-elim`, encapsulates the idea of _substituting equals for equals_, and is also a special form because it requires a bit of extra context. Its tableau looks like this.

$$\begin{array}{ccc}
x = y &                & P[z \mapsto x] \\ \hline
      & P[z \mapsto y] &
\end{array}$$

We interpret this rule as follows: $P[z \mapsto e]$ represents a judgement $P$ after the substitution $z \mapsto e$ has been applied, where $z$ is an expression variable and $e$ an expression. To check an invocation of this rule, we need four things: the variable $z$ being substituted for, the judgement $P$ being substituted into, the equality $x = y$, and the judgement $P[z \mapsto x]$. Let's see an example of `eq-elim` in action by proving that equality is symmetric.

~~~ {.mycelium}
theorem eq-sym
if
  * x == y
then
  * y == x

proof
1. x == x : eq-intro
2. x == y : assumption 1
3. y == x : eq-elim z (z == x); 2, 1
~~~

Note how the dummy variable $z$ doesn't actually appear in the judgements of the proof; it's just an artifact of `eq-elim`.

Here's another example: equality is transitive.

~~~ {.mycelium}
theorem eq-trans
if
  * x == y
  * y == z
then
  * x == z

proof
1. y == z : assumption 2
2. x == y : assumption 1
3. x == z : eq-elim w (x == w); 1, 2
~~~

A very clear and common method of proof, especially in algebra, is the _equation chain_. Say we have two things, $E_1$ and $E_n$, and want to show that they are equal. One way to do this is to exhibit a chain of things $E_2$, $E_3$, ..., $E_{n-1}$ and show that $E_1 = E_2$, $E_2 = E_3$, ..., $E_{n-1} = E_n$. Doing this in raw natural deduction is a little cumbersome compared to the way we'd write such a proof informally, because we have to explicitly invoke transitivity or eq-elim for each link in the chain. However, the sequence of these invocations follows a simple pattern.

Our proof checker understands an alternative syntax just for equation chains like this, invoked with the special evidence `chain`. Lets see an example.

~~~ {.mycelium}
theorem eq-trans-3
if
  * x == y
  * y == z
  * z == w
then
  * x == w

proof
1. x : chain
    == y : assumption 1
    == z : assumption 2
    == w : assumption 3
~~~

The syntax condenses an equation chain to a single "line" in the proof, where each equality is annotated with just its own justification. The entire line reduces to the statement that $x = w$. We can't refer back to individual equalities in the chain, but that is almost never necessary anyway. The full story behind equation chains is a little more complicated than this example demonstrates, but we're not ready to see their full power just yet. Suffice it to say for now that each successive `==` line in the proof for `eq-trans-3` gets expanded to about 4 lines of raw natural deduction that would otherwise require jumping around to follow.
