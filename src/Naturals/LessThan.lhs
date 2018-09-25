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


theorem lt-impl-leq
if
  * \lt(a)(b) == \true
then
  * \leq(a)(b) == \true

proof
1. \lt(a)(b) == \true
    : assumption 1
2. (\leq(a)(b) == \true) /\ (\eq(a)(b) == \false)
    : use lt-leq-eq-impl; 1
3. \leq(a)(b) == \true
    : use conj-elim-l; 2


theorem lt-impl-not-eq
if
  * \lt(a)(b) == \true
then
  * \eq(a)(b) == \false

proof
1. \lt(a)(b) == \true
    : assumption 1
2. (\leq(a)(b) == \true) /\ (\eq(a)(b) == \false)
    : use lt-leq-eq-impl; 1
3. \eq(a)(b) == \false
    : use conj-elim-r; 2


theorem lt-impl-not-leq
if
  * \lt(a)(b) == \true
then
  * \leq(b)(a) == \false

proof
1.  (\leq(b)(a) == \true) \/ (\leq(b)(a) == \false)
     : use bool-cases;

2.    \leq(b)(a) == \true : hypothesis t

3.    \lt(a)(b) == \true : assumption 1

4.    \leq(a)(b) == \true : use lt-impl-leq; 3

5.    a == b : use leq-antisym; 4, 2

6.    \true : chain
       == \eq(a)(b) : flop use eq-reify; 5
       == \false : use lt-impl-not-eq; 3

7.  (\leq(b)(a) == \true) =>
      (\true == \false)
     : discharge t; 6

8.  ~(\true == \false)
     : use bool-disc;

9.  ~(\leq(b)(a) == \true)
     : use modus-tollens; 7, 8

10. \leq(b)(a) == \false
     : use disj-syllogism-l; 1, 9
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

~~~ {.mycelium}
theorem plus-next-impl-lt
if
  * ∃k. b == \plus(a)(\next(k))
then
  * \lt(a)(b) == \true

proof
1.  ∃k. b == \plus(a)(\next(k)) : assumption 1
2.    b == \plus(a)(\next(u)) : hypothesis u
3.    ∃k. b == \plus(a)(k)
       : exists-intro k <- \next(u); 2
4.    \leq(a)(b) == \true
       : use plus-impl-leq; 3
5.      \eq(a)(b) == \true : hypothesis eq
6.      \plus(a)(\zero) : chain
         == a : use plus-zero-r;
         == b : use eq-dereify; 5
         == \plus(a)(\next(u))
          : hypothesis u
7.      \zero == \next(u)
         : use plus-cancel-l; 6
8.      ∃k. \zero == \next(k)
         : exists-intro k <- u; 7
9.    (\eq(a)(b) == \true) => (∃k. \zero == \next(k))
       : discharge eq; 8
10.   ~(∃k. \zero == \next(k))
       : use nat-disc;
11.   ~(\eq(a)(b) == \true)
       : use modus-tollens; 9, 10
12.   \not(\eq(a)(b)) : chain
       == \not(\false)
        : use not-eq-true; 11 at z in
          \not(z)
       == \true : use not-false;
13.   \lt(a)(b) : chain
       == \and(\leq(a)(b))(\not(\eq(a)(b)))
        : use def-lt;
       == \and(\leq(a)(b))(\true)
        : use reiterate; 12 at z in
          \and(\leq(a)(b))(z)
       == \and(\true)(\true)
        : use reiterate; 4 at z in
          \and(z)(\true)
       == \true
        : use and-true-true;
14. (b == \plus(a)(\next(u))) => (\lt(a)(b) == \true)
     : discharge u; 13
15. \lt(a)(b) == \true
     : exists-elim u <- k; 1, 14
~~~

~~~ {.mycelium}
theorem lt-trans
if
  * \lt(a)(b) == \true
  * \lt(b)(c) == \true
then
  * \lt(a)(c) == \true

proof
1.  \lt(a)(b) == \true : assumption 1
2.  ∃k. b == \plus(a)(\next(k)) : use lt-impl-plus-next; 1
3.    b == \plus(a)(\next(t)) : hypothesis t
4.    \lt(b)(c) == \true : assumption 2
5.    ∃k. c == \plus(b)(\next(k)) : use lt-impl-plus-next; 4
6.      c == \plus(b)(\next(u)) : hypothesis u
7.        c : chain
           == \plus(b)(\next(u))
            : hypothesis u
           == \plus(\plus(a)(\next(t)))(\next(u))
            : hypothesis t at z in
              \plus(z)(\next(u))
           == \plus(a)(\plus(\next(t))(\next(u)))
            : use plus-assoc-r;
           == \plus(a)(\next(\plus(t)(\next(u))))
            : use plus-next-l; at z in
              \plus(a)(z)
8.      ∃k. c == \plus(a)(\next(k))
         : exists-intro k <- \plus(t)(\next(u)); 7
9.    (c == \plus(b)(\next(u))) =>
        (∃k. c == \plus(a)(\next(k)))
       : discharge u; 8
10.   ∃k. c == \plus(a)(\next(k))
       : exists-elim u <- k; 5, 9
11. (b == \plus(a)(\next(t))) =>
      (∃k. c == \plus(a)(\next(k)))
     : discharge t; 10
12. ∃k. c == \plus(a)(\next(k))
     : exists-elim t <- k; 2, 11
13. \lt(a)(c) == \true
     : use plus-next-impl-lt; 12
~~~

~~~ {.mycelium}
theorem lt-trichotomy
* (\eq(a)(b) == \true) \/
    ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true))

proof
1.  (\eq(a)(b) == \true) \/ (\eq(a)(b) == \false)
     : use bool-cases;

2.    \eq(a)(b) == \true : hypothesis eq


3.    (\eq(a)(b) == \true) \/
        ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true))
       : use disj-intro-l; 2

4.  (\eq(a)(b) == \true) =>
      ((\eq(a)(b) == \true) \/
        ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true)))
     : discharge eq; 3

5.    \eq(a)(b) == \false : hypothesis neq

6.    \not(\eq(a)(b)) : chain
       == \not(\false)
        : hypothesis neq at z in \not(z)
       == \true
        : use not-false;

7.      (\leq(a)(b) == \true) \/ (\leq(a)(b) == \false)
         : use bool-cases;

8.        \leq(a)(b) == \true : hypothesis leq-t

9.        \lt(a)(b) : chain
           == \and(\leq(a)(b))(\not(\eq(a)(b)))
            : use def-lt;
           == \and(\leq(a)(b))(\true)
            : use reiterate; 6 at z in
              \and(\leq(a)(b))(z)
           == \and(\true)(\true)
            : hypothesis leq-t at z in
              \and(z)(\true)
           == \true
            : use and-true-true;

10.     (\lt(a)(b) == \true) \/ (\lt(b)(a) == \true)
         : use disj-intro-l; 9

11.     (\leq(a)(b) == \true) =>
          ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true))
         : discharge leq-t; 10

12.       \leq(a)(b) == \false : hypothesis leq-f

13.       \leq(b)(a) == \true : use leq-false-flip; 12

14.       \lt(b)(a) : chain
           == \and(\leq(b)(a))(\not(\eq(b)(a)))
            : use def-lt;
           == \and(\true)(\not(\eq(b)(a)))
            : use reiterate; 13 at z in
              \and(z)(\not(\eq(b)(a)))
           == \not(\eq(b)(a))
            : use and-true-l;
           == \not(\eq(a)(b))
            : use eq-comm; at z in \not(z)
           == \not(\false)
            : hypothesis neq at z in \not(z)
           == \true
            : use not-false;

15.     (\lt(a)(b) == \true) \/ (\lt(b)(a) == \true)
         : use disj-intro-r; 14

16.   (\leq(a)(b) == \false) =>
        ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true))
       : discharge leq-f; 15

17.   (\lt(a)(b) == \true) \/ (\lt(b)(a) == \true)
       : use disj-elim; 7, 11, 16

18.   (\eq(a)(b) == \true) \/
        ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true))
       : use disj-intro-r; 17

19. (\eq(a)(b) == \false) =>
      ((\eq(a)(b) == \true) \/
        ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true)))
     : discharge neq; 18

20. (\eq(a)(b) == \true) \/
      ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true))
     : use disj-elim; 1, 4, 19
~~~
