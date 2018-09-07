---
title: Either
---

$\Either\ a\ b$ acts like $\Pair$ with all the arrows reversed. Given types $a$ and $b$, there is a type $\Either\ a\ b$ and two functions $\lft : a \rightarrow \Either\ a\ b$ and $\rgt : b \rightarrow \Either\ a\ b$ with the property that if $x$ is a type and $\sigma : a \rightarrow x$ and $\tau : x \rightarrow b$ functions then there is a unique function $\either(\sigma)(\tau) : \Either\ a\ b \rightarrow x$ such that the following diagram commutes.

$$\require{AMScd}
\begin{CD}
a @>{\lft}>> \Either\ a\ b @<{\rgt}<< b \\
@V{\sigma}VV @VV{\either(\sigma)(\tau)}V @VV{\tau}V \\
x @= x @= x
\end{CD}$$

We can describe the types of $\lft$, $\rgt$, and $\either$.

~~~ {.mycelium}
type \lft :: a -> Either a b

type \rgt :: b -> Either a b

rule either-disc
* ~(∃a. (∃b. \lft(a) == \rgt(b)))

type \either :: (a -> t) -> (b -> t) -> Either a b -> t
~~~

Next, the commutativity of the diagram.

~~~ {.mycelium}
rule either-lft
* \either(f)(g)(\lft(a)) == f(a)

rule either-rgt
* \either(f)(g)(\rgt(b)) == g(b)
~~~

And the uniqueness of $\either$.

~~~ {.mycelium}
rule either-unique
if
  * \comp(h)(\lft) == f
  * \comp(h)(\rgt) == g
then
  * h == \either(f)(g)
~~~

And the induction principle for $\Either$.

~~~ {.mycelium}
rule either-induction
if
  * ∀a. ((m == \lft(a)) => P)
  * ∀b. ((m == \rgt(b)) => P)
then
  * P
~~~

From uniqueness, we can characterize $\id$ in terms of $\either$.

~~~ {.mycelium}
theorem either-lft-rgt
* \id == \either(\lft)(\rgt)

proof
1. \comp(\id)(\lft)(x) : chain
    == \id(\lft(x)) : use def-comp;
    == \lft(x) : use def-id;
2. ∀t. \comp(\id)(\lft)(t) == \lft(t)
    : forall-intro x -> t; 1
3. \comp(\id)(\lft) == \lft : use fun-eq; 2
4. \comp(\id)(\rgt)(x) : chain
    == \id(\rgt(x)) : use def-comp;
    == \rgt(x) : use def-id;
5. ∀t. \comp(\id)(\rgt)(t) == \rgt(t)
    : forall-intro x -> t; 4
6. \comp(\id)(\rgt) == \rgt : use fun-eq; 5
7. \id == \either(\lft)(\rgt)
    : use either-unique; 3, 6
~~~

Composition distributes over $\either$ from the left.

~~~ {.mycelium}
theorem comp-either-dist-l
* \comp(w)(\either(f)(g)) == \either(\comp(w)(f))(\comp(w)(g))

proof
1. \comp(\comp(w)(\either(f)(g)))(\lft)(a) : chain
    == \comp(w)(\either(f)(g))(\lft(a)) : use def-comp;
    == w(\either(f)(g)(\lft(a))) : use def-comp;
    == w(f(a)) : use either-lft; at z in w(z)
    == \comp(w)(f)(a) : flop use def-comp;
2. ∀x. \comp(\comp(w)(\either(f)(g)))(\lft)(x) == \comp(w)(f)(x)
    : forall-intro a -> x; 1
3. \comp(\comp(w)(\either(f)(g)))(\lft) == \comp(w)(f)
    : use fun-eq; 2
4. \comp(\comp(w)(\either(f)(g)))(\rgt)(a) : chain
    == \comp(w)(\either(f)(g))(\rgt(a)) : use def-comp;
    == w(\either(f)(g)(\rgt(a))) : use def-comp;
    == w(g(a)) : use either-rgt; at z in w(z)
    == \comp(w)(g)(a) : flop use def-comp;
5. ∀x. \comp(\comp(w)(\either(f)(g)))(\rgt)(x) == \comp(w)(g)(x)
    : forall-intro a -> x; 4
6. \comp(\comp(w)(\either(f)(g)))(\rgt) == \comp(w)(g)
    : use fun-eq; 5
7. \comp(w)(\either(f)(g)) == \either(\comp(w)(f))(\comp(w)(g))
    : use either-unique; 3, 6
~~~

Both $\lft$ and $\rgt$ are injective.

~~~ {.mycelium}
theorem lft-inj
if
  * \lft(a) == \lft(b)
then
  * a == b

proof
1. \true : chain
    == \eq(a)(a) : flop use eq-refl;
    == \either(\eq(a))(\const(\true))(\lft(a))
        : flop use either-lft;
    == \either(\eq(a))(\const(\true))(\lft(b))
        : assumption 1 at z in \either(\eq(a))(\const(\true))(z)
    == \eq(a)(b) : use either-lft;
2. \eq(a)(b) == \true : use eq-sym; 1
3. a == b : use eq-dereify; 2


theorem rgt-inj
if
  * \rgt(a) == \rgt(b)
then
  * a == b

proof
1. \true : chain
    == \eq(a)(a) : flop use eq-refl;
    == \either(\const(\true))(\eq(a))(\rgt(a))
        : flop use either-rgt;
    == \either(\const(\true))(\eq(a))(\rgt(b))
        : assumption 1 at z in \either(\const(\true))(\eq(a))(z)
    == \eq(a)(b) : use either-rgt;
2. \eq(a)(b) == \true : use eq-sym; 1
3. a == b : use eq-dereify; 2
~~~
