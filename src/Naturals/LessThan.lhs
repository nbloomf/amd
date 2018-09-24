---
title: Less Than
---

~~~ {.mycelium}
type \lt :: Nat -> Nat -> Bool

definition def-lt
* \lt(a)(b) == \and(\leq(a)(b))(\not(\eq(a)(b)))
~~~

~~~ {.mycelium}
theorem leq-eq-lt-impl
if
  * \leq(a)(b) == \true
  * \eq(a)(b) == \false
then
  * \lt(a)(b) == \true

proof
1. \lt(a)(b) : chain
    == \and(\leq(a)(b))(\not(\eq(a)(b)))
     : use def-lt;
    == \and(\true)(\not(\eq(a)(b)))
     : assumption 1 at z in
       \and(z)(\not(\eq(a)(b)))
    == \and(\true)(\not(\false))
     : assumption 2 at z in
       \and(\true)(\not(z))
    == \and(\true)(\true)
     : use not-false; at z in
       \and(\true)(z)
    == \true
     : use and-true-true;
~~~

~~~ {.mycelium}
theorem lt-leq-eq-impl
if
  * \lt(a)(b) == \true
then
  * (\leq(a)(b) == \true) /\ (\eq(a)(b) == \false)

proof
1. \and(\leq(a)(b))(\not(\eq(a)(b))) : chain
    == \lt(a)(b) : flop use def-lt;
    == \true : assumption 1
2. (\leq(a)(b) == \true) /\ (\not(\eq(a)(b)) == \true) : use and-conj; 1
3. \leq(a)(b) == \true : use conj-elim-l; 2
4. \not(\eq(a)(b)) == \true : use conj-elim-r; 2
5. \eq(a)(b) == \false : use not-true-impl; 4
6. (\leq(a)(b) == \true) /\ (\eq(a)(b) == \false)
    : use conj-intro; 3, 5
~~~

~~~ {.mycelium}
theorem lt-next-next
* \lt(\next(a))(\next(b)) == \lt(a)(b)

proof
1. \lt(\next(a))(\next(b)) : chain
    == \and(
         \leq(\next(a))(\next(b)))(
         \not(\eq(\next(a))(\next(b))))
     : use def-lt;
    == \and(\leq(a)(b))(\not(\eq(\next(a))(\next(b))))
     : use leq-next-next; at z in
       \and(z)(\not(\eq(\next(a))(\next(b))))
    == \and(\leq(a)(b))(\not(\eq(a)(b)))
     : use eq-next-next; at z in
       \and(\leq(a)(b))(\not(z))
    == \lt(a)(b)
     : flop use def-lt;
~~~

~~~ {.mycelium}
theorem not-lt-refl
* \lt(a)(a) == \false

proof
1.  \lt(a)(a) == \true : hypothesis t
2.  \and(\leq(a)(a))(\not(\eq(a)(a))) : chain
     == \lt(a)(a) : flop use def-lt;
     == \true : hypothesis t
3.  (\leq(a)(a) == \true) /\ (\not(\eq(a)(a)) == \true)
     : use and-conj; 2
4.  \not(\eq(a)(a)) == \true : use conj-elim-r; 3
5.  \true : chain
     == \not(\eq(a)(a)) : flop use reiterate; 4
     == \not(\true) : use eq-refl; at z in \not(z)
     == \false : use not-true;
6. (\lt(a)(a) == \true) => (\true == \false)
    : discharge t; 5
7. ~(\true == \false) : use bool-disc;
8. ~(\lt(a)(a) == \true) : use modus-tollens; 6, 7
9. \lt(a)(a) == \false : use not-eq-true; 8
~~~

~~~ {.mycelium}
theorem lt-impl-plus-next
if
  * \lt(a)(b) == \true
then
  * ∃k. b == \plus(a)(\next(k))

proof
1.  \lt(a)(b) == \true : assumption 1
2.  (\leq(a)(b) == \true) /\ (\eq(a)(b) == \false)
     : use lt-leq-eq-impl; 1
3.  \leq(a)(b) == \true : use conj-elim-l; 2
4.  \eq(a)(b) == \false : use conj-elim-r; 2
5.  ∃k. b == \plus(a)(k) : use leq-impl-plus; 3
6.    b == \plus(a)(t) : hypothesis t
7.    (t == \zero) \/ (∃u. t == \next(u))
       : use nat-disj-cases-1;
8.      t == \zero : hypothesis t-zero
9.      a : chain
         == \plus(a)(\zero) : flop use plus-zero-r;
         == \plus(a)(t)
          : flop hypothesis t-zero at z in
            \plus(a)(z)
         == b : flop hypothesis t
10.     \true : chain
         == \eq(a)(b) : flop use eq-reify; 9
         == \false : use reiterate; 4
11.   (t == \zero) => (\true == \false)
       : discharge t-zero; 10
12.   ~(\true == \false) : use bool-disc;
13.   ~(t == \zero) : use modus-tollens; 11, 12
14.   ∃u. t == \next(u) : use disj-syllogism-l; 7, 13
15.     t == \next(w) : hypothesis t-next-w
16.     b : chain
         == \plus(a)(t) : hypothesis t
         == \plus(a)(\next(w))
          : hypothesis t-next-w at z in
            \plus(a)(z)
17.     ∃k. b == \plus(a)(\next(k))
         : exists-intro k <- w; 16
18.   (t == \next(w)) => (∃k. b == \plus(a)(\next(k)))
       : discharge t-next-w; 17
19.   ∃k. b == \plus(a)(\next(k))
       : exists-elim w <- u; 14, 18
20. (b == \plus(a)(t)) => (∃k. b == \plus(a)(\next(k)))
     : discharge t; 19
21. ∃k. b == \plus(a)(\next(k))
     : exists-elim t <- k; 5, 20
~~~
