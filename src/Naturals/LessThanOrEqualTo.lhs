---
title: Less Than or Equal To
---

~~~ {.mycelium}
type \leq :: Nat -> Nat -> Bool

definition def-leq
* \leq(a)(b) == \opt(\false)(\const(\true))(\minus(b)(a))
~~~


~~~ {.mycelium}
theorem leq-refl
* \leq(a)(a) == \true

proof
1. \leq(a)(a) : chain
    == \opt(\false)(\const(\true))(\minus(a)(a))
        : use def-leq;
    == \opt(\false)(\const(\true))(\just(\zero))
        : use minus-self; at z in \opt(\false)(\const(\true))(z)
    == \const(\true)(\zero) : use opt-just;
    == \true : use def-const;


theorem eq-impl-leq
if
  * \eq(a)(b) == \true
then
  * \leq(a)(b) == \true

proof
1. \eq(a)(b) == \true : assumption 1

2. a == b : use eq-dereify; 1

3. \leq(a)(b) : chain
    == \leq(b)(b)
     : use reiterate; 2 at z in
       \leq(z)(b)
    == \true
     : use leq-refl;
~~~

~~~ {.mycelium}
theorem leq-zero-l
* \leq(\zero)(a) == \true

proof
1. \leq(\zero)(a) : chain
    == \opt(\false)(\const(\true))(\minus(a)(\zero))
     : use def-leq;
    == \opt(\false)(\const(\true))(\just(a))
     : use minus-zero-r; at z in
       \opt(\false)(\const(\true))(z)
    == \const(\true)(a)
     : use opt-just;
    == \true
     : use def-const;
~~~

~~~ {.mycelium}
theorem leq-impl-plus
if
  * \leq(a)(b) == \true
then
  * ∃k. b == \plus(a)(k)

proof
1.  (\minus(b)(a) == \nothing) \/ (∃u. \minus(b)(a) == \just(u))
     : use maybe-cases;

2.    \minus(b)(a) == \nothing : hypothesis nothing

3.    \true : chain
       == \leq(a)(b)
        : flop assumption 1
       == \opt(\false)(\const(\true))(\minus(b)(a))
        : use def-leq;
       == \opt(\false)(\const(\true))(\nothing)
        : hypothesis nothing at z in
          \opt(\false)(\const(\true))(z)
       == \false
        : use opt-nothing;

4.  (\minus(b)(a) == \nothing) => (\true == \false)
     : discharge nothing; 3

5.  ~(\true == \false) : use bool-disc;

6.  ~(\minus(b)(a) == \nothing) : use modus-tollens; 4, 5

7.  ∃u. \minus(b)(a) == \just(u) : use disj-syllogism-l; 1, 6

8.    \minus(b)(a) == \just(c) : hypothesis just

9.    b : chain
       == \plus(c)(a) : use minus-to-plus; 8
       == \plus(a)(c) : use plus-comm;


10.   ∃u. b == \plus(a)(u) : exists-intro u <- c; 9

11. (\minus(b)(a) == \just(c)) => (∃u. b == \plus(a)(u))
     : discharge just; 10

12. ∃u. b == \plus(a)(u) : exists-elim c <- u; 7, 11
~~~

~~~ {.mycelium}
theorem leq-next-zero
* \leq(\next(a))(\zero) == \false

proof
1.    \leq(\next(a))(\zero) == \true
       : hypothesis true

2.    ∃k. \zero == \plus(\next(a))(k)
       : use leq-impl-plus; 1

3.      \zero == \plus(\next(a))(u)
         : hypothesis zero-u

4.      \zero : chain
         == \plus(\next(a))(u)
          : hypothesis zero-u
         == \next(\plus(a)(u))
          : use plus-next-l;

5.      ∃k. \zero == \next(k)
         : exists-intro k <- \plus(a)(u); 4

6.    (\zero == \plus(\next(a))(u)) =>
        (∃k. \zero == \next(k))
       : discharge zero-u; 5

7.    ∃k. \zero == \next(k)
       : exists-elim u <- k; 2, 6

8.  (\leq(\next(a))(\zero) == \true) =>
      (∃k. \zero == \next(k))
     : discharge true; 7

9.  ~(∃k. \zero == \next(k)) : use nat-disc;

10. ~(\leq(\next(a))(\zero) == \true)
     : use modus-tollens; 8, 9

11. \leq(\next(a))(\zero) == \false
     : use not-eq-true; 10
~~~

~~~ {.mycelium}
theorem leq-zero-is-zero
if
  * \leq(a)(\zero) == \true
then
  * a == \zero

proof
1.  (a == \zero) \/ (∃k. a == \next(k))
     : use nat-disj-cases-1;

2.    ∃k. a == \next(k)
       : hypothesis next

3.      a == \next(t)
         : hypothesis a-next-t

4.      \true : chain
         == \leq(a)(\zero)
          : flop assumption 1
         == \leq(\next(t))(\zero)
          : hypothesis a-next-t at z in
            \leq(z)(\zero)
         == \false
          : use leq-next-zero;

5.    (a == \next(t)) => (\true == \false)
       : discharge a-next-t; 4

6.    \true == \false
       : exists-elim t <- k; 2, 5

7.  (∃k. a == \next(k)) => (\true == \false)
     : discharge next; 6

8.  ~(\true == \false)
     : use bool-disc;

9.  ~(∃k. a == \next(k))
     : use modus-tollens; 7, 8

10. a == \zero
     : use disj-syllogism-r; 1, 9
~~~

~~~ {.mycelium}
theorem leq-next-next
* \leq(\next(a))(\next(b)) == \leq(a)(b)

proof
1. \leq(\next(a))(\next(b)) : chain

    == \opt(\false)(\const(\true))(\minus(\next(b))(\next(a)))
     : use def-leq;

    == \opt(\false)(\const(\true))(\minus(b)(a))
     : use minus-next-next; at z in
       \opt(\false)(\const(\true))(z)

    == \leq(a)(b) : flop use def-leq;
~~~

~~~ {.mycelium}
theorem leq-next-self
* \leq(\next(a))(a) == \false

proof
1. \leq(\next(a))(a) : chain

    == \opt(\false)(\const(\true))(\minus(a)(\next(a)))
     : use def-leq;

    == \opt(\false)(\const(\true))(\nothing)
     : use minus-self-next; at z in
       \opt(\false)(\const(\true))(z)

    == \false : use opt-nothing;
~~~

~~~ {.mycelium}
theorem leq-self-plus
* \leq(a)(\plus(a)(b)) == \true

proof
1. \leq(a)(\plus(a)(b)) : chain

    == \opt(\false)(\const(\true))(\minus(\plus(a)(b))(a))
     : use def-leq;

    == \opt(\false)(\const(\true))(\just(b))
     : use minus-plus-inverse-l; at z in
       \opt(\false)(\const(\true))(z)

    == \const(\true)(b) : use opt-just;

    == \true : use def-const;
~~~

~~~ {.mycelium}
theorem plus-impl-leq
if
  * ∃k. b == \plus(a)(k)
then
  * \leq(a)(b) == \true

proof
1. ∃k. b == \plus(a)(k) : assumption 1

2.   b == \plus(a)(u) : hypothesis plus

3.   \leq(a)(b) : chain

      == \leq(a)(\plus(a)(u))
       : hypothesis plus at z in
         \leq(a)(z)

      == \true : use leq-self-plus;

4. (b == \plus(a)(u)) => (\leq(a)(b) == \true)
    : discharge plus; 3

5. \leq(a)(b) == \true : exists-elim u <- k; 1, 4
~~~

~~~ {.mycelium}
theorem leq-antisym
if
  * \leq(a)(b) == \true
  * \leq(b)(a) == \true
then
  * a == b

proof
1.  \leq(a)(b) == \true : assumption 1

2.  ∃k. b == \plus(a)(k) : use leq-impl-plus; 1

3.    b == \plus(a)(u) : hypothesis u

4.    \leq(b)(a) == \true : assumption 2

5.    ∃k. a == \plus(b)(k) : use leq-impl-plus; 4

6.      a == \plus(b)(v) : hypothesis v

7.      a : chain
         == \plus(b)(v)
          : hypothesis v
         == \plus(\plus(a)(u))(v)
          : hypothesis u at z in \plus(z)(v)
         == \plus(a)(\plus(u)(v))
          : use plus-assoc-r;

8.      \plus(u)(v) == \zero : use plus-self-cancel-l; 7

9.      (u == \zero) /\ (v == \zero) : use plus-eq-zero; 8

10.     u == \zero : use conj-elim-l; 9

11.     a : chain
         == \plus(a)(\zero)
          : flop use plus-zero-r;
         == \plus(a)(u)
          : flop use reiterate; 10 at z in
            \plus(a)(z)
         == b
          : flop hypothesis u

12.   (a == \plus(b)(v)) => (a == b) : discharge v; 11

13.   a == b : exists-elim v <- k; 5, 12

14. (b == \plus(a)(u)) => (a == b) : discharge u; 13

15. a == b : exists-elim u <- k; 2, 14
~~~

~~~ {.mycelium}
theorem leq-trans
if
  * \leq(a)(b) == \true
  * \leq(b)(c) == \true
then
  * \leq(a)(c) == \true

proof
1.  \leq(a)(b) == \true : assumption 1

2.  ∃k. b == \plus(a)(k) : use leq-impl-plus; 1

3.    b == \plus(a)(u) : hypothesis u

4.    \leq(b)(c) == \true : assumption 2

5.    ∃k. c == \plus(b)(k) : use leq-impl-plus; 4

6.      c == \plus(b)(v) : hypothesis v

7.      c : chain
         == \plus(b)(v)
          : hypothesis v
         == \plus(\plus(a)(u))(v)
          : hypothesis u at z in \plus(z)(v)
         == \plus(a)(\plus(u)(v))
          : use plus-assoc-r;

8.      ∃k. c == \plus(a)(k)
         : exists-intro k <- \plus(u)(v); 7

9.    (c == \plus(b)(v)) => (∃k. c == \plus(a)(k))
       : discharge v; 8

10.   ∃k. c == \plus(a)(k) : exists-elim v <- k; 5, 9

11. (b == \plus(a)(u)) => (∃k. c == \plus(a)(k))
     : discharge u; 10

12. ∃k. c == \plus(a)(k) : exists-elim u <- k; 2, 11

13. \leq(a)(c) == \true : use plus-impl-leq; 12
~~~

~~~ {.mycelium}
theorem leq-plus-cancel-r
* \leq(\plus(a)(c))(\plus(b)(c)) == \leq(a)(b)

proof
1. \leq(\plus(a)(c))(\plus(b)(c)) : chain

    == \opt(\false)(\const(\true))(
         \minus(\plus(b)(c))(\plus(a)(c)))
     : use def-leq;

    == \opt(\false)(\const(\true))(
         \minus(b)(a))
     : use minus-plus-cancel-r; at z in
       \opt(\false)(\const(\true))(z)

    == \leq(a)(b)
     : flop use def-leq;


theorem leq-plus-cancel-l
* \leq(\plus(c)(a))(\plus(c)(b)) == \leq(a)(b)

proof
1. \leq(\plus(c)(a))(\plus(c)(b)) : chain

    == \leq(\plus(a)(c))(\plus(c)(b))
     : use plus-comm; at z in
       \leq(z)(\plus(c)(b))

    == \leq(\plus(a)(c))(\plus(b)(c))
     : use plus-comm; at z in
       \leq(\plus(a)(c))(z)

    == \leq(a)(b)
     : use leq-plus-cancel-r;
~~~

~~~ {.mycelium}
theorem leq-plus-compat
if
  * \leq(a1)(b1) == \true
  * \leq(a2)(b2) == \true
then
  * \leq(\plus(a1)(a2))(\plus(b1)(b2)) == \true

proof
1. \leq(\plus(a1)(a2))(\plus(a1)(b2)) : chain
    == \leq(a2)(b2) : use leq-plus-cancel-l;
    == \true : assumption 2

2. \leq(\plus(a1)(b2))(\plus(b1)(b2)) : chain
    == \leq(a1)(b1) : use leq-plus-cancel-r;
    == \true : assumption 1

3. \leq(\plus(a1)(a2))(\plus(b1)(b2)) == \true
    : use leq-trans; 1, 2
~~~

~~~ {.mycelium}
theorem leq-false-flip
if
  * \leq(a)(b) == \false
then
  * \leq(b)(a) == \true

proof
1.  \leq(a)(b) == \false
     : assumption 1

2.  (\minus(b)(a) == \nothing) \/ (∃k. \minus(b)(a) == \just(k))
     : use maybe-cases;

3.    ∃k. \minus(b)(a) == \just(k)
       : hypothesis just

4.      \minus(b)(a) == \just(u)
         : hypothesis just-u

5.      \true : chain
         == \const(\true)(u)
          : flop use def-const;
         == \opt(\false)(\const(\true))(\just(u))
          : flop use opt-just;
         == \opt(\false)(\const(\true))(\minus(b)(a))
          : flop hypothesis just-u at z in
            \opt(\false)(\const(\true))(z)
         == \leq(a)(b)
          : flop use def-leq;
         == \false
          : assumption 1

6.    (\minus(b)(a) == \just(u)) => (\true == \false)
       : discharge just-u; 5

7.    \true == \false
       : exists-elim u <- k; 3, 6

8.  (∃k. \minus(b)(a) == \just(k)) => (\true == \false)
     : discharge just; 7

9.  ~(\true == \false)
     : use bool-disc;

10. ~(∃k. \minus(b)(a) == \just(k))
     : use modus-tollens; 8, 9

11. \minus(b)(a) == \nothing
     : use disj-syllogism-r; 2, 10

12. ∃k. \minus(a)(b) == \just(\next(k))
     : use minus-flip; 11

13.   \minus(a)(b) == \just(\next(t))
       : hypothesis t

14.   \leq(b)(a) : chain
       == \opt(\false)(\const(\true))(\minus(a)(b))
        : use def-leq;
       == \opt(\false)(\const(\true))(\just(\next(t)))
        : hypothesis t at z in
          \opt(\false)(\const(\true))(z)
       == \const(\true)(\next(t))
        : use opt-just;
       == \true
        : use def-const;

15. (\minus(a)(b) == \just(\next(t))) => (\leq(b)(a) == \true)
     : discharge t; 14

16. \leq(b)(a) == \true
     : exists-elim t <- k; 12, 15
~~~

~~~ {.mycelium}
theorem leq-next-cases
if
  * \leq(a)(\next(b)) == \true
then
  * (\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true)

proof
1.  \leq(a)(\next(b)) == \true
     : assumption 1

2.  ∃k. \next(b) == \plus(a)(k)
     : use leq-impl-plus; 1

3.    \next(b) == \plus(a)(t)
       : hypothesis t

4.    (t == \zero) \/ (∃k. t == \next(k))
       : use nat-disj-cases-1;

5.      t == \zero
         : hypothesis t-zero

6.      a : chain
         == \plus(a)(\zero)
          : flop use plus-zero-r;
         == \plus(a)(t)
          : flop hypothesis t-zero at z in
            \plus(a)(z)
         == \next(b)
          : flop use reiterate; 3

7.      \eq(a)(\next(b)) == \true
         : use eq-reify; 6

8.      (\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true)
         : use disj-intro-r; 7

9.    (t == \zero) =>
        ((\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true))
       : discharge t-zero; 8

10.     ∃k. t == \next(k)
         : hypothesis next

11.       t == \next(u)
           : hypothesis u

12.       \next(b) : chain
           == \plus(a)(t)
            : hypothesis t
           == \plus(a)(\next(u))
            : hypothesis u at z in
              \plus(a)(z)
           == \next(\plus(a)(u))
            : use plus-next-r;

13.       b == \plus(a)(u)
           : use next-inj; 12

14.       ∃k. b == \plus(a)(k)
           : exists-intro k <- u; 13

15.       \leq(a)(b) == \true
           : use plus-impl-leq; 14

16.       (\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true)
           : use disj-intro-l; 15

17.     (t == \next(u)) =>
          ((\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true))
         : discharge u; 16

18.     (\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true)
         : exists-elim u <- k; 10, 17

19.   (∃k. t == \next(k)) =>
        ((\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true))
       : discharge next; 18

20.   (\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true)
       : use disj-elim; 4, 9, 19

21. (\next(b) == \plus(a)(t)) =>
      ((\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true))
     : discharge t; 20

22. (\leq(a)(b) == \true) \/ (\eq(a)(\next(b)) == \true)
     : exists-elim t <- k; 2, 21
~~~
