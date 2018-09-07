---
title: Maybe
---

Our next inductive type is $\Maybe$, which behaves just like $a$ with an extra value tacked on. Regular $a$s are constructed with $\just$, and the extra value is called $\nothing$.

~~~ {.mycelium}
type \just :: a -> Maybe a

type \nothing :: Maybe a

rule maybe-disc
* ~(∃a. \nothing == \just(a))
~~~

We can think about $\Maybe$ as the initial algebra of the constant functor to $\Either\ \Unit\ a$, where $a$ is fixed, and we think of this functor as the pointwise sum of the constant functors to $\Unit$ and $a$.

$$\require{AMScd}
\begin{CD}
\Either\ \Unit\ a @>{\either(\only(\nothing))(\just)}>> \Maybe\ a \\
@V{\id}VV @VV{\opt(b)(f)}V \\
\Either\ \Unit\ a @>>{\either(\only(b))(f)}> x
\end{CD}$$

We'll call the universal arrow for $\Maybe\ a$ _opt_.

~~~ {.mycelium}
type \opt :: b -> (a -> b) -> Maybe a -> b
~~~

There are a few concrete ways to think about $\Maybe\ a$; it effectively adds a "default" or "missing" value to $a$. We need rules to express that $\opt$ is a homomorphism:

~~~ {.mycelium}
rule opt-nothing
* \opt(b)(f)(\nothing) == u

rule opt-just
* \opt(b)(f)(\just(a)) == f(a)
~~~

And a rule to express that $\opt$ is unique.

~~~ {.mycelium}
rule opt-unique
if
  * t(b)(f)(\nothing) == b
  * \comp(t(b)(f))(\just) == f
then
  * t == \opt
~~~

Finally, we have an induction principle.

~~~ {.mycelium}
rule maybe-induction
if
  * (m == \nothing) => P
  * ∀a. ((m == \just(a)) => P)
then
  * P
~~~
