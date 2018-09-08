---
title: Flip
---

All functions in the simply typed lambda calculus take only one argument; we can simulate functions of multiple arguments by making the _output_ another function. This imposes a strict order on the arguments. $\flip$ is a handy function that can rearrange another function's arguments.

~~~ {.mycelium}
type \flip :: (a -> b -> c) -> b -> a -> c

definition def-flip
* \flip(f)(b)(a) == f(a)(b)
~~~

$\flip$ is an involution:

~~~ {.mycelium}
theorem flip-invol
* \comp(\flip)(\flip) == \id

proof
1. \comp(\flip)(\flip)(f)(a)(b) : chain
    == \flip(\flip(f))(a)(b) : use def-comp; at w in w(a)(b)
    == \flip(f)(b)(a) : use def-flip;
    == f(a)(b) : use def-flip;
    == \id(f)(a)(b) : flop use def-id; at w in w(a)(b)
2. ∀v. \comp(\flip)(\flip)(f)(a)(v) == \id(f)(a)(v)
    : forall-intro b -> v; 1
3. \comp(\flip)(\flip)(f)(a) == \id(f)(a) : use fun-eq; 2
4. ∀v. \comp(\flip)(\flip)(f)(v) == \id(f)(v) : forall-intro a -> v; 3
5. \comp(\flip)(\flip)(f) == \id(f) : use fun-eq; 4
6. ∀v. \comp(\flip)(\flip)(v) == \id(v) : forall-intro f -> v; 5
7. \comp(\flip)(\flip) == \id : use fun-eq; 6
~~~

$\flip$ interacts with $\const$:

~~~ {.mycelium}
theorem flip-const
* \flip(\const) == \const(\id)

proof
1. \flip(\const)(b)(a) : chain
    == \const(a)(b) : use def-flip;
    == a : use def-const;
    == \id(a) : flop use def-id;
    == \const(\id)(b)(a) : flop use def-const; at f in f(a)
2. ∀x. \flip(\const)(b)(x) == \const(\id)(b)(x)
    : forall-intro a -> x; 1
3. \flip(\const)(b) == \const(\id)(b) : use fun-eq; 2
4. ∀x. \flip(\const)(x) == \const(\id)(x) : forall-intro b -> x; 3
5. \flip(\const) == \const(\id) : use fun-eq; 4
~~~

