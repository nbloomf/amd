---
title: Times
---

We can define $\times$ as iterated addition.

~~~ {.mycelium}
type \times :: Nat -> Nat -> Nat

definition def-times
* \times(a) == \natrec(\zero)(\plus(a))
~~~

We can characterize $\times$ as the unique solution to a system of equations.

~~~ {.mycelium}
theorem times-zero-r
* \times(a)(\zero) == \zero

proof
1. \times(a)(\zero) : chain
    == \natrec(\zero)(\plus(a))(\zero)
     : use def-times; at f in f(\zero)
    == \zero : use natrec-zero;


theorem times-next-r
* \times(a)(\next(b)) == \plus(a)(\times(a)(b))

proof
1. \times(a)(\next(b)) : chain
    == \natrec(\zero)(\plus(a))(\next(b))
     : use def-times; at f in f(\next(b))
    == \plus(a)(\natrec(\zero)(\plus(a))(b))
     : use natrec-next;
    == \plus(a)(\times(a)(b))
     : flop use def-times; at f in \plus(a)(f(b))
~~~

Now $\zero$ is a left zero for $\times$:

~~~ {.mycelium}
theorem times-zero-l
* \times(\zero)(b) == \zero

proof
1. \times(\zero)(\zero) : chain
    == \zero : use times-zero-r;

2.   \times(\zero)(n) == \zero : hypothesis n

3.   \times(\zero)(\next(n)) : chain
      == \natrec(\zero)(\plus(\zero))(\next(n))
       : use def-times; at f in f(\next(n))
      == \plus(\zero)(\natrec(\zero)(\plus(\zero))(n))
       : use natrec-next;
      == \natrec(\zero)(\plus(\zero))(n)
       : use plus-zero-l;
      == \times(\zero)(n)
       : flop use def-times; at f in f(n)
      == \zero
       : hypothesis n

4. (\times(\zero)(n) == \zero) =>
     (\times(\zero)(\next(n)) == \zero)
    : discharge n; 3

5. ∀k. (\times(\zero)(k) == \zero) =>
     (\times(\zero)(\next(k)) == \zero)
    : forall-intro n -> k; 4

6. ∀k. \times(\zero)(k) == \zero
    : invoke nat-induction
      [P :-> \times(\zero)(_) == \zero]; 1, 5

7. \times(\zero)(b) == \zero
    : forall-elim k -> b; 6
~~~

$\times$ interacts with $\next$ in the left argument.

~~~ {.mycelium}
theorem times-next-l
* \times(\next(a))(b) == \plus(b)(\times(a)(b))

proof
1. \times(\next(a))(\zero) : chain
    == \zero : use times-zero-r;
    == \times(a)(\zero) : flop use times-zero-r;
    == \plus(\zero)(\times(a)(\zero)) : flop use plus-zero-l;

2.   \times(\next(a))(n) == \plus(n)(\times(a)(n))
      : hypothesis n

3.   \times(\next(a))(\next(n)) : chain
      == \plus(\next(a))(\times(\next(a))(n))
       : use times-next-r;
      == \plus(\next(a))(\plus(n)(\times(a)(n)))
       : hypothesis n at z in \plus(\next(a))(z)
      == \plus(\plus(\next(a))(n))(\times(a)(n))
       : use plus-assoc-l;
      == \plus(\plus(a)(\next(n)))(\times(a)(n))
       : use plus-next; at z in \plus(z)(\times(a)(n))
      == \plus(\plus(\next(n))(a))(\times(a)(n))
       : use plus-comm; at z in \plus(z)(\times(a)(n))
      == \plus(\next(n))(\plus(a)(\times(a)(n)))
       : use plus-assoc-r;
      == \plus(\next(n))(\times(a)(\next(n)))
       : flop use times-next-r; at z in \plus(\next(n))(z)

4. (\times(\next(a))(n) == \plus(n)(\times(a)(n))) =>
     (\times(\next(a))(\next(n))
      == \plus(\next(n))(\times(a)(\next(n))))
    : discharge n; 3

5. ∀k. (\times(\next(a))(k) == \plus(k)(\times(a)(k))) =>
     (\times(\next(a))(\next(k))
      == \plus(\next(k))(\times(a)(\next(k))))
    : forall-intro n -> k; 4

6. ∀k. \times(\next(a))(k) == \plus(k)(\times(a)(k))
    : invoke nat-induction
      [P :-> \times(\next(a))(_) == \plus(_)(\times(a)(_))]; 1, 5

7. \times(\next(a))(b) == \plus(b)(\times(a)(b))
    : forall-elim k -> b; 6
~~~

$\times$ is commutative.

~~~ {.mycelium}
theorem times-comm
* \times(a)(b) == \times(b)(a)

proof
1. \times(a)(\zero) : chain
    == \zero : use times-zero-r;
    == \times(\zero)(a) : flop use times-zero-l;

2.   \times(a)(n) == \times(n)(a) : hypothesis n

3.   \times(a)(\next(n)) : chain
      == \plus(a)(\times(a)(n))
       : use times-next-r;
      == \plus(a)(\times(n)(a))
       : hypothesis n at z in \plus(a)(z)
      == \times(\next(n))(a)
       : flop use times-next-l;

4. (\times(a)(n) == \times(n)(a)) =>
     (\times(a)(\next(n)) == \times(\next(n))(a))
    : discharge n; 3

5. ∀k. (\times(a)(k) == \times(k)(a)) =>
     (\times(a)(\next(k)) == \times(\next(k))(a))
    : forall-intro n -> k; 4

6. ∀k. \times(a)(k) == \times(k)(a)
    : invoke nat-induction
      [P :-> \times(a)(_) == \times(_)(a)]; 1, 5

7. \times(a)(b) == \times(b)(a)
    : forall-elim k -> b; 6
~~~

$\times$ distributes over $\plus$.

~~~ {.mycelium}
theorem times-plus-dist-l
* \times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c))

proof
1.  \times(a)(\plus(b)(\zero)) : chain
     == \times(a)(b)
      : use plus-zero-r; at z in \times(a)(z)
     == \plus(\times(a)(b))(\zero)
      : flop use plus-zero-r;
     == \plus(\times(a)(b))(\times(a)(\zero))
      : flop use times-zero-r; at z in \plus(\times(a)(b))(z)

2.  ∀k. \times(a)(\plus(k)(\zero))
         == \plus(\times(a)(k))(\times(a)(\zero))
     : forall-intro b -> k; 1

3.    ∀k. \times(a)(\plus(k)(n))
           == \plus(\times(a)(k))(\times(a)(n))
       : hypothesis n

4.    \times(a)(\plus(\next(b))(n))
       == \plus(\times(a)(\next(b)))(\times(a)(n))
       : forall-elim k -> \next(b); 3

5.    \times(a)(\plus(b)(\next(n))) : chain
       == \times(a)(\plus(\next(b))(n))
        : flop use plus-next; at z in \times(a)(z)
       == \plus(\times(a)(\next(b)))(\times(a)(n))
        : use reiterate; 4
       == \plus(\plus(a)(\times(a)(b)))(\times(a)(n))
        : use times-next-r; at z in \plus(z)(\times(a)(n))
       == \plus(\plus(\times(a)(b))(a))(\times(a)(n))
        : use plus-comm; at z in \plus(z)(\times(a)(n))
       == \plus(\times(a)(b))(\plus(a)(\times(a)(n)))
        : use plus-assoc-r;
       == \plus(\times(a)(b))(\times(a)(\next(n)))
        : flop use times-next-r; at z in \plus(\times(a)(b))(z)

6.    ∀k. \times(a)(\plus(k)(\next(n)))
       == \plus(\times(a)(k))(\times(a)(\next(n)))
        : forall-intro b -> k; 5

7.  (∀k. \times(a)(\plus(k)(n))
       == \plus(\times(a)(k))(\times(a)(n))) =>
      (∀k. \times(a)(\plus(k)(\next(n)))
       == \plus(\times(a)(k))(\times(a)(\next(n))))
     : discharge n; 6

8.  ∀u. (∀k. \times(a)(\plus(k)(u))
         == \plus(\times(a)(k))(\times(a)(u))) =>
      (∀k. \times(a)(\plus(k)(\next(u)))
       == \plus(\times(a)(k))(\times(a)(\next(u))))
     : forall-intro n -> u; 7

9.  ∀u. (∀k. \times(a)(\plus(k)(u))
     == \plus(\times(a)(k))(\times(a)(u)))
      : invoke nat-induction
        [P :-> ∀k. \times(a)(\plus(k)(_))
         == \plus(\times(a)(k))(\times(a)(_))]; 2, 8

10. ∀k. \times(a)(\plus(k)(c)) == \plus(\times(a)(k))(\times(a)(c))
     : forall-elim u -> c; 9

11. \times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c))
     : forall-elim k -> b; 10


theorem times-plus-dist-r
* \times(\plus(b)(c))(a) == \plus(\times(b)(a))(\times(c)(a))

proof
1. \times(\plus(b)(c))(a) : chain

    == \times(a)(\plus(b)(c))
     : use times-comm;

    == \plus(\times(a)(b))(\times(a)(c))
     : use times-plus-dist-l;

    == \plus(\times(b)(a))(\times(a)(c))
     : use times-comm; at z in
       \plus(z)(\times(a)(c))

    == \plus(\times(b)(a))(\times(c)(a))
     : use times-comm; at z in
       \plus(\times(b)(a))(z)
~~~

$\times$ is associative.

~~~ {.mycelium}
theorem times-assoc-l
* \times(a)(\times(b)(c)) == \times(\times(a)(b))(c)

proof
1. \times(a)(\times(b)(\zero)) : chain
    == \times(a)(\zero)
     : use times-zero-r; at z in \times(a)(z)
    == \zero
     : use times-zero-r;
    == \times(\times(a)(b))(\zero)
     : flop use times-zero-r;

2.   \times(a)(\times(b)(n)) == \times(\times(a)(b))(n)
      : hypothesis n

3.   \times(a)(\times(b)(\next(n))) : chain
      == \times(a)(\plus(b)(\times(b)(n)))
       : use times-next-r; at z in \times(a)(z)
      == \plus(\times(a)(b))(\times(a)(\times(b)(n)))
       : use times-plus-dist-l;
      == \plus(\times(a)(b))(\times(\times(a)(b))(n))
       : hypothesis n at z in \plus(\times(a)(b))(z)
      == \times(\times(a)(b))(\next(n))
       : flop use times-next-r;

4. (\times(a)(\times(b)(n)) == \times(\times(a)(b))(n)) =>
     (\times(a)(\times(b)(\next(n))) == \times(\times(a)(b))(\next(n)))
    : discharge n; 3

5. ∀k. (\times(a)(\times(b)(k)) == \times(\times(a)(b))(k)) =>
     (\times(a)(\times(b)(\next(k))) == \times(\times(a)(b))(\next(k)))
    : forall-intro n -> k; 4

6. ∀k. \times(a)(\times(b)(k)) == \times(\times(a)(b))(k)
    : invoke nat-induction
      [P :-> \times(a)(\times(b)(_)) == \times(\times(a)(b))(_)]; 1, 5

7. \times(a)(\times(b)(c)) == \times(\times(a)(b))(c)
    : forall-elim k -> c; 6


theorem times-assoc-r
* \times(\times(a)(b))(c) == \times(a)(\times(b)(c))

proof
1. \times(a)(\times(b)(c)) == \times(\times(a)(b))(c)
    : use times-assoc-l;
2. \times(\times(a)(b))(c) == \times(a)(\times(b)(c))
    : use eq-sym; 1
~~~

$\next(\zero)$ is neutral for $\times.

~~~ {.mycelium}
theorem times-one-r
* \times(a)(\next(\zero)) == a

proof
1. \times(a)(\next(\zero)) : chain
    == \plus(a)(\times(a)(\zero)) : use times-next-r;
    == \plus(a)(\zero) : use times-zero-r; at z in \plus(a)(z)
    == a : use plus-zero-r;


theorem times-one-l
* \times(\next(\zero))(a) == a

proof
1. \times(\next(\zero))(a) : chain
    == \times(a)(\next(\zero)) : use times-comm;
    == a : use times-one-r;
~~~

If $\times(a)(b) = \zero$, then either $a = \zero$ or $b = \zero$.

~~~ {.mycelium}
theorem times-zerodivisor
if
  * \times(a)(b) == \zero
then
  * (a == \zero) \/ (b == \zero)

proof
1.  (a == \zero) \/ (∃k. a == \next(k))
     : use nat-disj-cases-1;

2.    a == \zero : hypothesis a-zero

3.    (a == \zero) \/ (b == \zero) : use disj-intro-l; 2

4.  (a == \zero) => ((a == \zero) \/ (b == \zero))
     : discharge a-zero; 3

5.    ∃k. a == \next(k) : hypothesis a-next

6.      a == \next(t) : hypothesis a-next-t

7.      (b == \zero) \/ (∃k. b == \next(k)) : use nat-disj-cases-1;

8.        ∃k. b == \next(k) : hypothesis b-next

9.          b == \next(u) : hypothesis b-next-u

10.         \zero : chain
             == \times(a)(b)
              : flop assumption 1
             == \times(\next(t))(b)
              : hypothesis a-next-t at z in \times(z)(b)
             == \times(\next(t))(\next(u))
              : hypothesis b-next-u at z in \times(\next(t))(z)
             == \plus(\next(t))(\times(\next(t))(u))
              : use times-next-r;
             == \next(\plus(t)(\times(\next(t))(u)))
              : use plus-next-l;

11.         ∃k. \zero == \next(k)
             : exists-intro k <- \plus(t)(\times(\next(t))(u)); 10

12.       (b == \next(u)) => (∃k. \zero == \next(k))
           : discharge b-next-u; 11

13.       ∃k. \zero == \next(k)
           : exists-elim u <- k; 8, 12

14.     (∃k. b == \next(k)) => (∃k. \zero == \next(k))
         : discharge b-next; 13

15.     ~(∃k. \zero == \next(k)) : use nat-disc;

16.     ~(∃k. b == \next(k)) : use modus-tollens; 14, 15

17.     b == \zero : use disj-syllogism-r; 7, 16

18.     (a == \zero) \/ (b == \zero)
         : use disj-intro-r; 17

19.   (a == \next(t)) => ((a == \zero) \/ (b == \zero))
       : discharge a-next-t; 18

20.   (a == \zero) \/ (b == \zero)
       : exists-elim t <- k; 5, 19

21. (∃k. a == \next(k)) => ((a == \zero) \/ (b == \zero))
     : discharge a-next; 20

22. (a == \zero) \/ (b == \zero) : use disj-elim; 1, 4, 21
~~~

As a special case of the previous theorem, if $\times(a)(\next(b)) = \zero$, then $a = \zero$.

~~~ {.mycelium}
theorem times-is-zero-l
if
  * \times(a)(\next(b)) == \zero
then
  * a == \zero

proof
1. \times(a)(\next(b)) == \zero : assumption 1
2. (a == \zero) \/ (\next(b) == \zero) : use times-zerodivisor; 1
3.   \next(b) == \zero : hypothesis b
4.   \zero == \next(b) : use eq-sym; 3
5.   ∃k. \zero == \next(k) : exists-intro k <- b; 4
6. (\next(b) == \zero) => (∃k. \zero == \next(k)) : discharge b; 5
7. ~(∃k. \zero == \next(k)) : use nat-disc;
8. ~(\next(b) == \zero) : use modus-tollens; 6, 7
9. a == \zero : use disj-syllogism-r; 2, 8
~~~

And $\times$ is _almost_ cancellative.

~~~ {.mycelium}
theorem times-cancel-r
if
  * \times(a)(\next(c)) == \times(b)(\next(c))
then
  * a == b

proof
1.    \times(\zero)(\next(c)) == \times(w)(\next(c)) : hypothesis zero

2.    \times(b)(\next(c)) : chain
       == \times(\zero)(\next(c)) : flop hypothesis zero
       == \zero : use times-zero-l;

3.    \zero : chain
       == b : flop use times-is-zero-l; 2

4.  (\times(\zero)(\next(c)) == \times(b)(\next(c))) => (\zero == b)
     : discharge zero; 3

5.  ∀w. (\times(\zero)(\next(c)) == \times(w)(\next(c))) => (\zero == w)
     : forall-intro b -> w; 4

6.    ∀w. (\times(n)(\next(c)) == \times(w)(\next(c))) => (n == w)
       : hypothesis n

7.      \times(\next(n))(\next(c)) == \times(b)(\next(c))
         : hypothesis next

8.      (b == \zero) \/ (∃k. b == \next(k))
         : use nat-disj-cases-1;

9.        b == \zero : hypothesis b-zero

10.        \zero : chain
            == \times(\zero)(\next(c))
             : flop use times-zero-l;
            == \times(b)(\next(c))
             : flop hypothesis b-zero at z in \times(z)(\next(c))
            == \times(\next(n))(\next(c))
             : flop hypothesis next
            == \plus(\next(n))(\times(\next(n))(c))
             : use times-next-r;
            == \next(\plus(n)(\times(\next(n))(c)))
             : use plus-next-l;

11.       ∃k. \zero == \next(k)
           : exists-intro k <- \plus(n)(\times(\next(n))(c)); 10

12.     (b == \zero) => (∃k. \zero == \next(k))
         : discharge b-zero; 11

13.     ~(∃k. \zero == \next(k)) : use nat-disc;

14.     ~(b == \zero) : use modus-tollens; 12, 13

15.     ∃k. b == \next(k) : use disj-syllogism-l; 8, 14

16.       b == \next(t) : hypothesis b-next-t

17.       \plus(\next(c))(\times(n)(\next(c))) : chain
           == \times(\next(n))(\next(c))
            : flop use times-next-l;
           == \times(b)(\next(c))
            : hypothesis next
           == \times(\next(t))(\next(c))
            : hypothesis b-next-t at z in \times(z)(\next(c))
           == \plus(\next(c))(\times(t)(\next(c)))
            : use times-next-l;

18.       \times(n)(\next(c)) == \times(t)(\next(c))
           : use plus-cancel-l; 17

19.       (\times(n)(\next(c)) == \times(t)(\next(c))) => (n == t)
           : forall-elim w -> t; 6

20.       n == t : use impl-elim; 18, 19

21.       \next(n) : chain
           == \next(t) : use reiterate; 20 at z in \next(z)
           == b : flop hypothesis b-next-t

22.     (b == \next(t)) => (\next(n) == b) : discharge b-next-t; 21

23.     \next(n) == b : exists-elim t <- k; 15, 22

24.   (\times(\next(n))(\next(c))
       == \times(b)(\next(c))) => (\next(n) == b)
        : discharge next; 23

25.   ∀w. (\times(\next(n))(\next(c))
           == \times(w)(\next(c))) => (\next(n) == w)
       : forall-intro b -> w; 24

26. (∀w. (\times(n)(\next(c))
          == \times(w)(\next(c))) => (n == w)) =>
      (∀w. (\times(\next(n))(\next(c))
       == \times(w)(\next(c))) => (\next(n) == w))
     : discharge n; 25

27. ∀k. (∀w. (\times(k)(\next(c))
              == \times(w)(\next(c))) => (k == w)) =>
      (∀w. (\times(\next(k))(\next(c))
            == \times(w)(\next(c))) => (\next(k) == w))
     : forall-intro n -> k; 26

28. ∀k. (∀w. (\times(k)(\next(c))
              == \times(w)(\next(c))) => (k == w))
     : invoke nat-induction
       [P :-> ∀w. (\times(_)(\next(c))
                   == \times(w)(\next(c))) => (_ == w)]; 5, 27

29. ∀w. (\times(a)(\next(c)) == \times(w)(\next(c))) => (a == w)
     : forall-elim k -> a; 28

30. (\times(a)(\next(c)) == \times(b)(\next(c))) => (a == b)
     : forall-elim w -> b; 29

31. \times(a)(\next(c)) == \times(b)(\next(c))
     : assumption 1

32. a == b : use impl-elim; 31, 30


theorem times-cancel-l
if
  * \times(\next(c))(a) == \times(\next(c))(b)
then
  * a == b

proof
1. \times(a)(\next(c)) : chain
    == \times(\next(c))(a) : use times-comm;
    == \times(\next(c))(b) : assumption 1
    == \times(b)(\next(c)) : use times-comm;
2. a == b : use times-cancel-r; 1
~~~
