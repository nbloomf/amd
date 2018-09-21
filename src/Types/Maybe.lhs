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
  * t(\nothing) == b
  * \comp(t)(\just) == f
then
  * t == \opt(b)(f)
~~~

Finally, we have an induction principle.

~~~ {.mycelium}
rule maybe-induction
if
  * P[_ :-> \nothing]
  * ∀a. P[_ :-> \just(a)]
then
  * ∀u. P[_ :-> u]
~~~

~~~ {.mycelium}
theorem maybe-cases
* (x == \nothing) \/ (∃u. x == \just(u))

proof
1. \nothing == \nothing : eq-intro
2. (\nothing == \nothing) \/ (∃u. \nothing == \just(u)) : use disj-intro-l; 1
3. \just(a) == \just(a) : eq-intro
4. ∃u. \just(a) == \just(u) : exists-intro u <- a; 3
5. (\just(a) == \nothing) \/ (∃u. \just(a) == \just(u)) : use disj-intro-r; 4
6. ∀v. (\just(v) == \nothing) \/ (∃u. \just(v) == \just(u)) : forall-intro a -> v; 5
7. ∀w. (w == \nothing) \/ (∃u. w == \just(u))
    : invoke maybe-induction [P :-> (_ == \nothing) \/ (∃u. _ == \just(u))]; 2, 6
8. (x == \nothing) \/ (∃u. x == \just(u)) : forall-elim w -> x; 7
~~~

$\just$ is injective.

~~~ {.mycelium}
theorem just-inj
if
  * \just(a) == \just(b)
then
  * a == b

proof
1. \true : chain
    == \eq(a)(a) : flop use eq-refl;
    == \opt(\true)(\eq(a))(\just(a)) : flop use opt-just;
    == \opt(\true)(\eq(a))(\just(b))
        : assumption 1 at z in \opt(\true)(\eq(a))(z)
    == \eq(a)(b) : use opt-just;
2. \eq(a)(b) == \true : use eq-sym; 1
3. a == b : use eq-dereify; 2
~~~
