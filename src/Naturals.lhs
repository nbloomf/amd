---
title: Natural Numbers
---

We can define the natural numbers $\Nat$ as the initial $F$-algebra for the functor $F(x) = \Either\ \Unit\ x$. The algebra map $m : \Either\ \Unit\ \Nat \rightarrow \Nat$ has two components, $\zero$ and $\next$.

~~~ {.mycelium}
type \zero :: Nat

type \next :: Nat -> Nat

rule nat-disc
* ~(\zero == \next(n))
~~~

The unique homomorphism from $\Nat$ to some other $F$-algebra is denoted $\natrec$, and is the unique map making the following diagram commute.

$$\require{AMScd}
\begin{CD}
\Either\ \Unit\ \Nat @>{\either(\only(\zero))(\next)}>> \Nat \\
@V{\id}VV @VV{\natrec(e)(f)}V \\
\Either\ \Unit\ a @>>{\either(\only(e))(f)}> a
\end{CD}$$

The signature of $\natrec$ looks like this.

~~~ {.mycelium}
type \natrec :: a -> (a -> a) -> Nat -> a
~~~

We need rules to say that $\natrec$ is an $F$-algebra homomorphism:

~~~ {.mycelium}
rule natrec-zero
* \natrec(e)(f)(\zero) == e

rule natrec-next
* \natrec(e)(f)(\next(n)) == f(\natrec(e)(f)(n))
~~~

And a rule to say that $\natrec$ is unique.

~~~ {.mycelium}
rule natrec-unique
if
  * t(\zero) == e
  * \comp(t)(\next) == \comp(f)(t)
then
  * t == \natrec(e)(f)
~~~

Finally, we need an induction principle for $\Nat$.

~~~ {.mycelium}
rule nat-induction
if
  * (k == \zero) => P
  * ∀n. ((k == n) => P) => ((k == \next(n)) => P)
then
  * P
~~~

Using the uniqueness of $\natrec$, we can characterize $\id$ as an $F$-algebra homomorphism.

~~~ {.mycelium}
theorem natrec-zero-next
* \id == \natrec(\zero)(\next)

proof
1. \id(\zero) == \zero : use def-id;
2. \comp(\id)(\next) : chain
    == \next : use comp-id-l;
    == \comp(\next)(\id) : flop use comp-id-r;
3. \id == \natrec(\zero)(\next) : use natrec-unique; 1, 2
~~~
