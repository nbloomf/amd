---
title: Clone
---

$\clone$ is a helper function that duplicates function arguments.

~~~ {.mycelium}
type \clone :: (a -> a -> b) -> a -> b

definition def-clone
* \clone(f)(a) == f(a)(a)
~~~

$\clone$ absorbs $\flip$ from the left.

~~~ {.mycelium}
theorem clone-flip
* \comp(\clone)(\flip) == \clone

proof
1. \comp(\clone)(\flip)(f)(x) : chain
    == \clone(\flip(f))(x) : use def-comp; at h in h(x)
    == \flip(f)(x)(x) : use def-clone;
    == f(x)(x) : use def-flip;
    == \clone(f)(x) : flop use def-clone;
2. ∀u. \comp(\clone)(\flip)(f)(u) == \clone(f)(u)
    : forall-intro x -> u; 1
3. \comp(\clone)(\flip)(f) == \clone(f) : use fun-eq; 2
4. ∀v. \comp(\clone)(\flip)(v) == \clone(v)
    : forall-intro f -> v; 3
5. \comp(\clone)(\flip) == \clone : use fun-eq; 4
~~~
