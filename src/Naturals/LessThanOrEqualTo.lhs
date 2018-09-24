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
