---
title: Divides
---

~~~ {.mycelium}
type \div :: Nat -> Nat -> Bool

definition def-div
* \div(a)(b) == \eq(\zero)(\rem(b)(a))
~~~

~~~ {.mycelium}
theorem div-zero-r
* \div(a)(\zero) == \true

proof
1. \div(a)(\zero) : chain
    == \eq(\zero)(\rem(\zero)(a))
     : use def-div;
    == \eq(\zero)(\snd(\divalg(\zero)(a)))
     : use def-rem; at z in
       \eq(\zero)(z)
    == \eq(\zero)(\snd(\tup(\zero)(\zero)))
     : use divalg-zero-l; at z in
       \eq(\zero)(\snd(z))
    == \eq(\zero)(\zero)
     : use snd-tup; at z in
       \eq(\zero)(z)
    == \true
     : use eq-refl;
~~~

~~~ {.mycelium}
theorem div-zero-l
if
  * \div(\zero)(a) == \true
then
  * a == \zero

proof
1. \true : chain
    == \div(\zero)(a)
     : flop assumption 1
    == \eq(\zero)(\rem(a)(\zero))
     : use def-div;
    == \eq(\zero)(\snd(\divalg(a)(\zero)))
     : use def-rem; at z in
       \eq(\zero)(z)
    == \eq(\zero)(\snd(\tup(\zero)(a)))
     : use divalg-zero-r; at z in
       \eq(\zero)(\snd(z))
    == \eq(\zero)(a)
     : use snd-tup; at z in
       \eq(\zero)(z)
    == \eq(a)(\zero)
     : use eq-comm;

2. \eq(a)(\zero) : chain
    == \true
     : flop use reiterate; 1

3. a == \zero
    : use eq-dereify; 2
~~~

~~~ {.mycelium}
theorem div-impl-times
if
  * \div(a)(b) == \true
then
  * ∃k. b == \times(a)(k)

proof
1.  (a == \zero) \/ (∃u. a == \next(u))
     : use nat-disj-cases-1;

2.    a == \zero
       : hypothesis zero

3.    \div(\zero)(b) : chain
       == \div(a)(b)
        : flop hypothesis zero at z in
          \div(z)(b)
       == \true
        : assumption 1

4.    b : chain
       == \zero
        : use div-zero-l; 3
       == \times(\zero)(\zero)
        : flop use times-zero-l;
       == \times(a)(\zero)
        : flop hypothesis zero at z in
          \times(z)(\zero)

5.    ∃k. b == \times(a)(k)
       : exists-intro k <- \zero; 4

6.  (a == \zero) => (∃k. b == \times(a)(k))
     : discharge zero; 5

7.    ∃u. a == \next(u)
       : hypothesis next

8.      a == \next(t)
         : hypothesis next-t

9.      \eq(\zero)(\rem(b)(\next(t))) : chain
         == \eq(\zero)(\rem(b)(a))
          : flop hypothesis next-t at z in
            \eq(\zero)(\rem(b)(z))
         == \div(a)(b)
          : flop use def-div;
         == \true
          : assumption 1

10.     b : chain
         == \plus(\times(\quo(b)(\next(t)))(\next(t)))(\rem(b)(\next(t)))
          : use divalg-decomp;
         == \plus(\times(\quo(b)(\next(t)))(\next(t)))(\zero)
          : flop use eq-dereify; 9 at z in
            \plus(\times(\quo(b)(\next(t)))(\next(t)))(z)
         == \times(\quo(b)(\next(t)))(\next(t))
          : use plus-zero-r;
         == \times(\next(t))(\quo(b)(\next(t)))
          : use times-comm;
         == \times(a)(\quo(b)(\next(t)))
          : flop hypothesis next-t at z in
            \times(z)(\quo(b)(\next(t)))

11.     ∃k. b == \times(a)(k)
         : exists-intro k <- \quo(b)(\next(t)); 10

12.   (a == \next(t)) => (∃k. b == \times(a)(k))
       : discharge next-t; 11

13.   ∃k. b == \times(a)(k)
       : exists-elim t <- u; 7, 12

14. (∃u. a == \next(u)) => (∃k. b == \times(a)(k))
     : discharge next; 13

15. ∃k. b == \times(a)(k)
     : use disj-elim; 1, 6, 14
~~~

~~~ {.mycelium}
theorem times-impl-div
if
  * ∃k. b == \times(a)(k)
then
  * \div(a)(b) == \true

proof
1.  ∃k. b == \times(a)(k)
     : assumption 1

2.    b == \times(a)(u)
       : hypothesis u

3.    (a == \zero) \/ (∃k. a == \next(k))
       : use nat-disj-cases-1;

4.      a == \zero
         : hypothesis zero

5.      b : chain
         == \times(a)(u)
          : hypothesis u
         == \times(\zero)(u)
          : hypothesis zero at z in
            \times(z)(u)
         == \zero
          : use times-zero-l;

6.      \div(a)(b) : chain
         == \div(a)(\zero)
          : use reiterate; 5 at z in
            \div(a)(z)
         == \true
          : use div-zero-r;

7.    (a == \zero) => (\div(a)(b) == \true)
       : discharge zero; 6

8.      ∃k. a == \next(k)
         : hypothesis next

9.        a == \next(t)
           : hypothesis next-t

10.       b : chain
           == \times(a)(u)
            : hypothesis u
           == \times(\next(t))(u)
            : hypothesis next-t at z in
              \times(z)(u)
           == \times(u)(\next(t))
            : use times-comm;
           == \plus(\times(u)(\next(t)))(\zero)
            : flop use plus-zero-r;

11.       \leq(\zero)(t) == \true
           : use leq-zero-l;

12.       \divalg(b)(\next(t)) == \tup(u)(\zero)
           : use divalg-unique; 10, 11

13.       \div(a)(b) : chain
           == \eq(\zero)(\rem(b)(a))
            : use def-div;
           == \eq(\zero)(\snd(\divalg(b)(a)))
            : use def-rem; at z in
              \eq(\zero)(z)
           == \eq(\zero)(\snd(\divalg(b)(\next(t))))
            : hypothesis next-t at z in
              \eq(\zero)(\snd(\divalg(b)(z)))
           == \eq(\zero)(\snd(\tup(u)(\zero)))
            : use reiterate; 12 at z in
              \eq(\zero)(\snd(z))
           == \eq(\zero)(\zero)
            : use snd-tup; at z in
              \eq(\zero)(z)
           == \true
            : use eq-refl;

14.     (a == \next(t)) => (\div(a)(b) == \true)
         : discharge next-t; 13

15.     \div(a)(b) == \true
         : exists-elim t <- k; 8, 14

16.   (∃k. a == \next(k)) => (\div(a)(b) == \true)
       : discharge next; 15

17.   \div(a)(b) == \true
       : use disj-elim; 3, 7, 16

18. (b == \times(a)(u)) => (\div(a)(b) == \true)
     : discharge u; 17

19. \div(a)(b) == \true
     : exists-elim u <- k; 1, 18
~~~

~~~ {.mycelium}
theorem div-refl
* \div(a)(a) == \true

proof
1. a : chain
    == \times(a)(\next(\zero))
     : flop use times-one-r;

2. ∃k. a == \times(a)(k)
    : exists-intro k <- \next(\zero); 1

3. \div(a)(a) == \true
    : use times-impl-div; 2
~~~

~~~ {.mycelium}
theorem div-sym
if
  * \div(a)(b) == \true
  * \div(b)(a) == \true
then
  * a == b

proof
1.  (a == \zero) \/ (∃k. a == \next(k))
     : use nat-disj-cases-1;

2.    a == \zero
       : hypothesis a-zero

3.      (\div(a)(b) == \true) /\ (\div(b)(a) == \true)
         : hypothesis a-div

4.      \div(\zero)(b) : chain
         == \div(a)(b)
          : flop hypothesis a-zero at z in
            \div(z)(b)
         == \true
          : use conj-elim-l; 3

5.      b == \zero
         : use div-zero-l; 4

6.      a : chain
         == \zero
          : hypothesis a-zero
         == b
          : flop use reiterate; 5

7.    ((\div(a)(b) == \true) /\ (\div(b)(a) == \true)) =>
        (a == b)
       : discharge a-div; 6

8.  (a == \zero) =>
      (((\div(a)(b) == \true) /\ (\div(b)(a) == \true)) =>
        (a == b))
     : discharge a-zero; 7

9.    ∃k. a == \next(k)
       : hypothesis a-next

10.     a == \next(t)
         : hypothesis a-next-t

11.       (\div(a)(b) == \true) /\ (\div(b)(a) == \true)
           : hypothesis a-div

12.       \div(a)(b) == \true
           : use conj-elim-l; 11

13.       ∃k. b == \times(a)(k)
           : use div-impl-times; 12

14.         b == \times(a)(u)
             : hypothesis b-times

15.         \div(b)(a) == \true
             : use conj-elim-r; 11

16.         ∃k. a == \times(b)(k)
             : use div-impl-times; 15

17.           a == \times(b)(v)
               : hypothesis a-times

18.           \times(\next(t))(\next(\zero)) : chain
               == \next(t)
                : use times-one-r;
               == a
                : flop hypothesis a-next-t
               == \times(b)(v)
                : hypothesis a-times
               == \times(\times(a)(u))(v)
                : hypothesis b-times at z in
                  \times(z)(v)
               == \times(a)(\times(u)(v))
                : use times-assoc-r;
               == \times(\next(t))(\times(u)(v))
                : hypothesis a-next-t at z in
                  \times(z)(\times(u)(v))

19.           \next(\zero) == \times(u)(v)
               : use times-cancel-l; 18

20.           \times(u)(v) == \next(\zero)
               : use eq-sym; 19

21.           (u == \next(\zero)) /\ (v == \next(\zero))
               : use times-eq-one; 20

22.           v == \next(\zero)
               : use conj-elim-r; 21

23.           a : chain
               == \times(b)(v)
                : hypothesis a-times
               == \times(b)(\next(\zero))
                : use reiterate; 22 at z in
                  \times(b)(z)
               == b
                : use times-one-r;

24.         (a == \times(b)(v)) => (a == b)
             : discharge a-times; 23

25.         a == b
             : exists-elim v <- k; 16, 24

26.       (b == \times(a)(u)) => (a == b)
           : discharge b-times; 25

27.       a == b
           : exists-elim u <- k; 13, 26

28.     ((\div(a)(b) == \true) /\ (\div(b)(a) == \true)) => (a == b)
         : discharge a-div; 27

29.   (a == \next(t)) => (((\div(a)(b) == \true) /\ (\div(b)(a) == \true)) => (a == b))
       : discharge a-next-t; 28

30.   ((\div(a)(b) == \true) /\ (\div(b)(a) == \true)) => (a == b)
       : exists-elim t <- k; 9, 29

31. (∃k. a == \next(k)) =>
      (((\div(a)(b) == \true) /\ (\div(b)(a) == \true)) => (a == b))
     : discharge a-next; 30

32. ((\div(a)(b) == \true) /\ (\div(b)(a) == \true)) => (a == b)
     : use disj-elim; 1, 8, 31

33. \div(a)(b) == \true
     : assumption 1

34. \div(b)(a) == \true
     : assumption 2

35. (\div(a)(b) == \true) /\ (\div(b)(a) == \true)
     : use conj-intro; 33, 34

36. a == b
     : use impl-elim; 35, 32
~~~
