---
title: Eq
---

We'll also need a function that can convert judgement-level equality to value-level boolean.

~~~ {.mycelium}
type \eq :: a -> a -> Bool

rule def-eq
* (\eq(a)(b) == \true) <=> (a == b)
~~~

I like to think of $\eq$ as performing a sort of _reification_ of equality.

~~~ {.mycelium}
theorem eq-reify
if
  * a == b
then
  * \eq(a)(b) == \true

proof
1. a == b : assumption 1
2. (\eq(a)(b) == \true) <=> (a == b) : use def-eq;
3. (a == b) => (\eq(a)(b) == \true) : use equiv-elim-l; 2
4. \eq(a)(b) == \true : use impl-elim; 1, 3


theorem eq-dereify
if
  * \eq(a)(b) == \true
then
  * a == b

proof
1. \eq(a)(b) == \true : assumption 1
2. (\eq(a)(b) == \true) <=> (a == b) : use def-eq;
3. (\eq(a)(b) == \true) => (a == b) : use equiv-elim-r; 2
4. a == b : use impl-elim; 1, 3
~~~

The usual properties of equality hold for $\eq$. It's reflexive:

~~~ {.mycelium}
theorem eq-refl
* \eq(a)(a) == \true

proof
1. a == a : eq-intro
2. \eq(a)(a) == \true : use eq-reify; 1
~~~

$\eq$ is symmetric:

~~~ {.mycelium}
theorem eq-reify-sym
if
  * \eq(a)(b) == \true
then
  * \eq(b)(a) == \true

proof
1. \eq(a)(b) == \true : assumption 1
2. a == b : use eq-dereify; 1
3. b == a : use eq-sym; 2
4. \eq(b)(a) == \true : use eq-reify; 3
~~~

And $\eq$ is transitive.

~~~ {.mycelium}
theorem eq-reify-trans
if
  * \eq(a)(b) == \true
  * \eq(b)(c) == \true
then
  * \eq(a)(c) == \true

proof
1. \eq(a)(b) == \true : assumption 1
2. \eq(b)(c) == \true : assumption 2
3. a == b : use eq-dereify; 1
4. b == c : use eq-dereify; 2
5. a == c : use eq-trans; 3, 4
6. \eq(a)(c) == \true : use eq-reify; 5
~~~
