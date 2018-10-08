---
title: Division Algorithm
---

~~~ {.mycelium}
type \divalgH :: Nat -> Nat -> Pair Nat Nat -> Pair Nat Nat

definition def-divalgH
* \divalgH(b)(a)(x) == \if(
    \tup(\next(\fst(x)))(\zero))(
    \tup(\fst(x))(\next(\snd(x))))(
    \eq(b)(\next(\snd(x))))


type \divalg :: Nat -> Nat -> Pair Nat Nat

definition def-divalg
* \divalg == \flip(\simprec(\const(\tup(\zero)(\zero)))(\divalgH))
~~~

~~~ {.mycelium}
type \quo :: Nat -> Nat -> Nat

definition def-quo
* \quo(a)(b) == \fst(\divalg(a)(b))


type \rem :: Nat -> Nat -> Nat

definition def-rem
* \rem(a)(b) == \snd(\divalg(a)(b))
~~~

~~~ {.mycelium}
theorem divalg-quo-rem
* \divalg(a)(b) == \tup(\quo(a)(b))(\rem(a)(b))

proof
1. \divalg(a)(b) : chain
    == \tup(\fst(\divalg(a)(b)))(\snd(\divalg(a)(b)))
     : flop use tup-id;
    == \tup(\quo(a)(b))(\snd(\divalg(a)(b)))
     : flop use def-quo; at z in
       \tup(z)(\snd(\divalg(a)(b)))
    == \tup(\quo(a)(b))(\rem(a)(b))
     : flop use def-rem; at z in
       \tup(\quo(a)(b))(z)
~~~

~~~ {.mycelium}
theorem divalg-zero-l
* \divalg(\zero)(b) == \tup(\zero)(\zero)

proof
1. \divalg(\zero)(b) : chain
    == \flip(\simprec(\const(\tup(\zero)(\zero)))(\divalgH))(\zero)(b)
     : use def-divalg; at f in f(\zero)(b)
    == \simprec(\const(\tup(\zero)(\zero)))(\divalgH)(b)(\zero)
     : use def-flip;
    == \const(\tup(\zero)(\zero))(b)
     : use simprec-zero;
    == \tup(\zero)(\zero)
     : use def-const;
~~~

~~~ {.mycelium}
theorem divalg-zero-r
* \divalg(a)(\zero) == \tup(\zero)(a)

proof
1.  \divalg(\zero)(\zero) : chain
     == \tup(\zero)(\zero)
      : use divalg-zero-l;

2.    \divalg(n)(\zero) == \tup(\zero)(n)
       : hypothesis n

3.    \divalg(\next(n))(\zero) : chain
       == \flip(\simprec(\const(\tup(\zero)(\zero)))(\divalgH))(\next(n))(\zero)
        : use def-divalg; at f in f(\next(n))(\zero)
       == \simprec(\const(\tup(\zero)(\zero)))(\divalgH)(\zero)(\next(n))
        : use def-flip;
       == \divalgH(\zero)(n)(\simprec(\const(\tup(\zero)(\zero)))(\divalgH)(\zero)(n))
        : use simprec-next;
       == \divalgH(\zero)(n)(\flip(\simprec(\const(\tup(\zero)(\zero)))(\divalgH))(n)(\zero))
        : flop use def-flip; at z in
          \divalgH(\zero)(n)(z)
       == \divalgH(\zero)(n)(\divalg(n)(\zero))
        : flop use def-divalg; at z in
          \divalgH(\zero)(n)(z(n)(\zero))
       == \divalgH(\zero)(n)(\tup(\zero)(n))
        : hypothesis n at z in
          \divalgH(\zero)(n)(z)
       == \if(
            \tup(\next(\fst(\tup(\zero)(n))))(\zero))(
            \tup(\fst(\tup(\zero)(n)))(\next(\snd(\tup(\zero)(n)))))(
            \eq(\zero)(\next(\snd(\tup(\zero)(n)))))
        : use def-divalgH;
       == \if(
            \tup(\next(\fst(\tup(\zero)(n))))(\zero))(
            \tup(\fst(\tup(\zero)(n)))(\next(\snd(\tup(\zero)(n)))))(
            \false)
        : use bool-disc-eq; at z in
          \if(
            \tup(\next(\fst(\tup(\zero)(n))))(\zero))(
            \tup(\fst(\tup(\zero)(n)))(\next(\snd(\tup(\zero)(n)))))(
            z)
       == \tup(\fst(\tup(\zero)(n)))(\next(\snd(\tup(\zero)(n))))
        : use if-false;
       == \tup(\zero)(\next(\snd(\tup(\zero)(n))))
        : use fst-tup; at z in
          \tup(z)(\next(\snd(\tup(\zero)(n))))
       == \tup(\zero)(\next(n))
        : use snd-tup; at z in
          \tup(\zero)(\next(z))

4.  (\divalg(n)(\zero) == \tup(\zero)(n)) =>
      (\divalg(\next(n))(\zero) == \tup(\zero)(\next(n)))
     : discharge n; 3

5.  ∀k. (\divalg(k)(\zero) == \tup(\zero)(k)) =>
      (\divalg(\next(k))(\zero) == \tup(\zero)(\next(k)))
     : forall-intro n -> k; 4

6.  ∀k. \divalg(k)(\zero) == \tup(\zero)(k)
     : invoke nat-induction
       [P :-> \divalg(_)(\zero) == \tup(\zero)(_)]; 1, 5

7.  \divalg(a)(\zero) == \tup(\zero)(a)
     : forall-elim k -> a; 6
~~~

~~~ {.mycelium}
theorem divalg-exists
if
  * \divalg(a)(\next(b)) == \tup(q)(r)
then
  * (a == \plus(\times(q)(\next(b)))(r)) /\ (\leq(r)(b) == \true)

proof
1.    \divalg(\zero)(\next(b)) == \tup(q)(r) : hypothesis zero

2.    \tup(q)(r) : chain
       == \divalg(\zero)(\next(b))
        : flop hypothesis zero
       == \tup(\zero)(\zero)
        : use divalg-zero-l;

3.    (q == \zero) /\ (r == \zero)
       : use tup-eq-1; 2

4.    q == \zero : use conj-elim-l; 3

5.    r == \zero : use conj-elim-r; 3

6.    \zero : chain
       == \plus(\zero)(\zero)
        : flop use plus-zero-l;
       == \plus(\times(\zero)(\next(b)))(\zero)
        : flop use times-zero-l; at z in
          \plus(z)(\zero)
       == \plus(\times(q)(\next(b)))(\zero)
        : flop use reiterate; 4 at z in
          \plus(\times(z)(\next(b)))(\zero)
       == \plus(\times(q)(\next(b)))(r)
        : flop use reiterate; 5 at z in
          \plus(\times(q)(\next(b)))(z)

7.    \leq(r)(b) : chain
       == \leq(\zero)(b)
        : use reiterate; 5 at z in
          \leq(z)(b)
       == \true
        : use leq-zero-l;

8.    (\zero == \plus(\times(q)(\next(b)))(r)) /\
        (\leq(r)(b) == \true)
       : use conj-intro; 6, 7

9.  (\divalg(\zero)(\next(b)) == \tup(q)(r)) =>
      ((\zero == \plus(\times(q)(\next(b)))(r)) /\
        (\leq(r)(b) == \true))
     : discharge zero; 8

10. ∀v. (\divalg(\zero)(\next(b)) == \tup(q)(v)) =>
      ((\zero == \plus(\times(q)(\next(b)))(v)) /\
        (\leq(v)(b) == \true))
     : forall-intro r -> v; 9

11. ∀u. (∀v. (\divalg(\zero)(\next(b)) == \tup(u)(v)) =>
      ((\zero == \plus(\times(u)(\next(b)))(v)) /\
        (\leq(v)(b) == \true)))
     : forall-intro q -> u; 10

12.   ∀u. (∀v. (\divalg(n)(\next(b)) == \tup(u)(v)) =>
        ((n == \plus(\times(u)(\next(b)))(v)) /\
          (\leq(v)(b) == \true)))
       : hypothesis n

13.   ∀v. (\divalg(n)(\next(b)) == \tup(\quo(n)(\next(b)))(v)) =>
        ((n == \plus(\times(\quo(n)(\next(b)))(\next(b)))(v)) /\
          (\leq(v)(b) == \true))
       : forall-elim u -> \quo(n)(\next(b)); 12

14.   (\divalg(n)(\next(b)) == \tup(\quo(n)(\next(b)))(\rem(n)(\next(b)))) =>
        ((n == \plus(\times(\quo(n)(\next(b)))(\next(b)))(\rem(n)(\next(b)))) /\
          (\leq(\rem(n)(\next(b)))(b) == \true))
       : forall-elim v -> \rem(n)(\next(b)); 13

15.   \divalg(n)(\next(b)) == \tup(\quo(n)(\next(b)))(\rem(n)(\next(b)))
       : use divalg-quo-rem;

16.   (n == \plus(\times(\quo(n)(\next(b)))(\next(b)))(\rem(n)(\next(b)))) /\
        (\leq(\rem(n)(\next(b)))(b) == \true)
       : use impl-elim; 15, 14

17.   n == \plus(\times(\quo(n)(\next(b)))(\next(b)))(\rem(n)(\next(b)))
       : use conj-elim-l; 16

18.   \leq(\rem(n)(\next(b)))(b) == \true
       : use conj-elim-r; 16

19.     \divalg(\next(n))(\next(b)) == \tup(q)(r)
         : hypothesis next

20.     (\eq(\next(b))(\next(\rem(n)(\next(b)))) == \true) \/
          (\eq(\next(b))(\next(\rem(n)(\next(b)))) == \false)
         : use bool-cases;

21.       \eq(\next(b))(\next(\rem(n)(\next(b)))) == \true
           : hypothesis t

22.       \tup(q)(r) : chain
           == \divalg(\next(n))(\next(b))
            : flop hypothesis next
           == \flip(\simprec(\const(\tup(\zero)(\zero)))(\divalgH))(\next(n))(\next(b))
            : use def-divalg; at f in
              f(\next(n))(\next(b))
           == \simprec(\const(\tup(\zero)(\zero)))(\divalgH)(\next(b))(\next(n))
            : use def-flip;
           == \divalgH(\next(b))(n)(\simprec(\const(\tup(\zero)(\zero)))(\divalgH)(\next(b))(n))
            : use simprec-next;
           == \divalgH(\next(b))(n)(\flip(\simprec(\const(\tup(\zero)(\zero)))(\divalgH))(n)(\next(b)))
            : flop use def-flip; at z in
              \divalgH(\next(b))(n)(z)
           == \divalgH(\next(b))(n)(\divalg(n)(\next(b)))
            : flop use def-divalg; at z in
              \divalgH(\next(b))(n)(z(n)(\next(b)))
           == \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                \eq(\next(b))(\next(\snd(\divalg(n)(\next(b))))))
            : use def-divalgH;
           == \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                \eq(\next(b))(\next(\rem(n)(\next(b)))))
            : flop use def-rem; at z in
              \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                \eq(\next(b))(\next(z)))
           == \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                \true)
            : hypothesis t at z in
              \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                z)
           == \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero)
            : use if-true;
           == \tup(\next(\quo(n)(\next(b))))(\zero)
            : flop use def-quo; at z in
              \tup(\next(z))(\zero)

23.       (q == \next(\quo(n)(\next(b)))) /\ (r == \zero)
           : use tup-eq-1; 22

24.       q == \next(\quo(n)(\next(b)))
           : use conj-elim-l; 23

25.       r == \zero
           : use conj-elim-r; 23

26.       \next(b) == \next(\rem(n)(\next(b)))
           : use eq-dereify; 21

27.       \next(n) : chain
           == \next(\plus(\times(\quo(n)(\next(b)))(\next(b)))(\rem(n)(\next(b))))
            : use reiterate; 17 at z in
              \next(z)
           == \plus(\times(\quo(n)(\next(b)))(\next(b)))(\next(\rem(n)(\next(b))))
            : flop use plus-next-r;
           == \plus(\times(\quo(n)(\next(b)))(\next(b)))(\next(b))
            : flop use reiterate; 26 at z in
              \plus(\times(\quo(n)(\next(b)))(\next(b)))(z)
           == \plus(\next(b))(\times(\quo(n)(\next(b)))(\next(b)))
            : use plus-comm;
           == \times(\next(\quo(n)(\next(b))))(\next(b))
            : flop use times-next-l;
           == \times(q)(\next(b))
            : flop use reiterate; 24 at z in
              \times(z)(\next(b))
           == \plus(\times(q)(\next(b)))(\zero)
            : flop use plus-zero-r;
           == \plus(\times(q)(\next(b)))(r)
            : flop use reiterate; 25 at z in
              \plus(\times(q)(\next(b)))(z)

28.       \leq(r)(b) : chain
           == \leq(\zero)(b)
            : use reiterate; 25 at z in \leq(z)(b)
           == \true
            : use leq-zero-l;

29.       (\next(n) == \plus(\times(q)(\next(b)))(r)) /\ (\leq(r)(b) == \true)
           : use conj-intro; 27, 28

30.     (\eq(\next(b))(\next(\rem(n)(\next(b)))) == \true) =>
          ((\next(n) == \plus(\times(q)(\next(b)))(r)) /\ (\leq(r)(b) == \true))
         : discharge t; 29

31.       \eq(\next(b))(\next(\rem(n)(\next(b)))) == \false
           : hypothesis f

32.       \tup(q)(r) : chain
           == \divalg(\next(n))(\next(b))
            : flop hypothesis next
           == \flip(\simprec(\const(\tup(\zero)(\zero)))(\divalgH))(\next(n))(\next(b))
            : use def-divalg; at f in
              f(\next(n))(\next(b))
           == \simprec(\const(\tup(\zero)(\zero)))(\divalgH)(\next(b))(\next(n))
            : use def-flip;
           == \divalgH(\next(b))(n)(\simprec(\const(\tup(\zero)(\zero)))(\divalgH)(\next(b))(n))
            : use simprec-next;
           == \divalgH(\next(b))(n)(\flip(\simprec(\const(\tup(\zero)(\zero)))(\divalgH))(n)(\next(b)))
            : flop use def-flip; at z in
              \divalgH(\next(b))(n)(z)
           == \divalgH(\next(b))(n)(\divalg(n)(\next(b)))
            : flop use def-divalg; at z in
              \divalgH(\next(b))(n)(z(n)(\next(b)))
           == \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                \eq(\next(b))(\next(\snd(\divalg(n)(\next(b))))))
            : use def-divalgH;
           == \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                \eq(\next(b))(\next(\rem(n)(\next(b)))))
            : flop use def-rem; at z in
              \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                \eq(\next(b))(\next(z)))
           == \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                \false)
            : hypothesis f at z in
              \if(
                \tup(\next(\fst(\divalg(n)(\next(b)))))(\zero))(
                \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b))))))(
                z)
           == \tup(\fst(\divalg(n)(\next(b))))(\next(\snd(\divalg(n)(\next(b)))))
            : use if-false;
           == \tup(\quo(n)(\next(b)))(\next(\snd(\divalg(n)(\next(b)))))
            : flop use def-quo; at z in
              \tup(z)(\next(\snd(\divalg(n)(\next(b)))))
           == \tup(\quo(n)(\next(b)))(\next(\rem(n)(\next(b))))
            : flop use def-rem; at z in
              \tup(\quo(n)(\next(b)))(\next(z))

33.       (q == \quo(n)(\next(b))) /\ (r == \next(\rem(n)(\next(b))))
           : use tup-eq-1; 32

34.       q == \quo(n)(\next(b))
           : use conj-elim-l; 33

35.       r == \next(\rem(n)(\next(b)))
           : use conj-elim-r; 33

36.       \next(n) : chain
           == \next(\plus(\times(\quo(n)(\next(b)))(\next(b)))(\rem(n)(\next(b))))
            : use reiterate; 17 at z in
              \next(z)
           == \plus(\times(\quo(n)(\next(b)))(\next(b)))(\next(\rem(n)(\next(b))))
            : flop use plus-next-r;
           == \plus(\times(\quo(n)(\next(b)))(\next(b)))(r)
            : flop use reiterate; 35 at z in
              \plus(\times(\quo(n)(\next(b)))(\next(b)))(z)
           == \plus(\times(q)(\next(b)))(r)
            : flop use reiterate; 34 at z in
              \plus(\times(z)(\next(b)))(r)

37.       \leq(\next(\rem(n)(\next(b))))(\next(b)) : chain
           == \leq(\rem(n)(\next(b)))(b) : use leq-next-next;
           == \true : use reiterate; 18

38.       \eq(\next(\rem(n)(\next(b))))(\next(b)) : chain
           == \eq(\next(b))(\next(\rem(n)(\next(b))))
            : use eq-comm;
           == \false
            : hypothesis f

39.       \leq(r)(b) : chain
           == \leq(\next(\rem(n)(\next(b))))(b)
            : use reiterate; 35 at z in
              \leq(z)(b)
           == \true
            : use leq-eq-next-r; 37, 38

40.       (\next(n) == \plus(\times(q)(\next(b)))(r)) /\ (\leq(r)(b) == \true)
           : use conj-intro; 36, 39

41.     (\eq(\next(b))(\next(\rem(n)(\next(b)))) == \false) =>
          ((\next(n) == \plus(\times(q)(\next(b)))(r)) /\ (\leq(r)(b) == \true))
         : discharge f; 40

42.     (\next(n) == \plus(\times(q)(\next(b)))(r)) /\ (\leq(r)(b) == \true)
         : use disj-elim; 20, 30, 41

43.   (\divalg(\next(n))(\next(b)) == \tup(q)(r)) =>
        ((\next(n) == \plus(\times(q)(\next(b)))(r)) /\ (\leq(r)(b) == \true))
       : discharge next; 42

44.   ∀v. (\divalg(\next(n))(\next(b)) == \tup(q)(v)) =>
        ((\next(n) == \plus(\times(q)(\next(b)))(v)) /\ (\leq(v)(b) == \true))
       : forall-intro r -> v; 43

45.   ∀u. (∀v. (\divalg(\next(n))(\next(b)) == \tup(u)(v)) =>
        ((\next(n) == \plus(\times(u)(\next(b)))(v)) /\ (\leq(v)(b) == \true)))
       : forall-intro q -> u; 44

46. (∀u. (∀v. (\divalg(n)(\next(b)) == \tup(u)(v)) =>
        ((n == \plus(\times(u)(\next(b)))(v)) /\
          (\leq(v)(b) == \true)))) =>
      (∀u. (∀v. (\divalg(\next(n))(\next(b)) == \tup(u)(v)) =>
        ((\next(n) == \plus(\times(u)(\next(b)))(v)) /\
          (\leq(v)(b) == \true))))
     : discharge n; 45

47. ∀k. ((∀u. (∀v. (\divalg(k)(\next(b)) == \tup(u)(v)) =>
        ((k == \plus(\times(u)(\next(b)))(v)) /\
          (\leq(v)(b) == \true)))) =>
      (∀u. (∀v. (\divalg(\next(k))(\next(b)) == \tup(u)(v)) =>
        ((\next(k) == \plus(\times(u)(\next(b)))(v)) /\
          (\leq(v)(b) == \true)))))
     : forall-intro n -> k; 46

48. ∀k. (∀u. (∀v. (\divalg(k)(\next(b)) == \tup(u)(v)) =>
      ((k == \plus(\times(u)(\next(b)))(v)) /\
        (\leq(v)(b) == \true))))
     : invoke nat-induction
       [P :-> ∀u. (∀v. (\divalg(_)(\next(b)) == \tup(u)(v)) =>
                ((_ == \plus(\times(u)(\next(b)))(v)) /\
                  (\leq(v)(b) == \true)))]; 11, 47

49. ∀u. (∀v. (\divalg(a)(\next(b)) == \tup(u)(v)) =>
      ((a == \plus(\times(u)(\next(b)))(v)) /\
        (\leq(v)(b) == \true)))
     : forall-elim k -> a; 48

50. ∀v. (\divalg(a)(\next(b)) == \tup(q)(v)) =>
      ((a == \plus(\times(q)(\next(b)))(v)) /\
        (\leq(v)(b) == \true))
     : forall-elim u -> q; 49

51. (\divalg(a)(\next(b)) == \tup(q)(r)) =>
      ((a == \plus(\times(q)(\next(b)))(r)) /\
        (\leq(r)(b) == \true))
     : forall-elim v -> r; 50

52. \divalg(a)(\next(b)) == \tup(q)(r)
     : assumption 1

53. (a == \plus(\times(q)(\next(b)))(r)) /\
      (\leq(r)(b) == \true)
     : use impl-elim; 52, 51
~~~

~~~ {.mycelium}
theorem divalg-decomp
* a == \plus(\times(\quo(a)(\next(b)))(\next(b)))(\rem(a)(\next(b)))

proof
1. \divalg(a)(\next(b)) == \tup(\quo(a)(\next(b)))(\rem(a)(\next(b)))
    : use divalg-quo-rem;

2. (a == \plus(\times(\quo(a)(\next(b)))(\next(b)))(\rem(a)(\next(b)))) /\
     (\leq(\rem(a)(\next(b)))(b) == \true)
    : use divalg-exists; 1

3. a == \plus(\times(\quo(a)(\next(b)))(\next(b)))(\rem(a)(\next(b)))
    : use conj-elim-l; 2
~~~

~~~ {.mycelium}
theorem divalg-bound
* \leq(\rem(a)(\next(b)))(b) == \true

proof
1. \divalg(a)(\next(b)) == \tup(\quo(a)(\next(b)))(\rem(a)(\next(b)))
    : use divalg-quo-rem;

2. (a == \plus(\times(\quo(a)(\next(b)))(\next(b)))(\rem(a)(\next(b)))) /\
     (\leq(\rem(a)(\next(b)))(b) == \true)
    : use divalg-exists; 1

3. \leq(\rem(a)(\next(b)))(b) == \true
    : use conj-elim-r; 2
~~~

~~~ {.mycelium}
theorem divalg-unique-lemma
if
  * \plus(\times(a1)(\next(b)))(c1) == \plus(\times(a2)(\next(b)))(c2)
  * \leq(c1)(b) == \true
  * \leq(c2)(b) == \true
then
  * (a1 == a2) /\ (c1 == c2)

proof
1.    (\plus(\times(\zero)(\next(b)))(c1) == \plus(\times(a2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))
       : hypothesis zero

2.    \plus(\times(\zero)(\next(b)))(c1) == \plus(\times(a2)(\next(b)))(c2)
       : use conj-elim-l; 1

3.    (\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true)
       : use conj-elim-r; 1

4.    \leq(c1)(b) == \true
       : use conj-elim-l; 3

5.    \leq(c2)(b) == \true
       : use conj-elim-r; 3

6.    c1 : chain
       == \plus(\zero)(c1)
        : flop use plus-zero-l;
       == \plus(\times(\zero)(\next(b)))(c1)
        : flop use times-zero-l; at z in
          \plus(z)(c1)
       == \plus(\times(a2)(\next(b)))(c2)
        : use reiterate; 2

7.    (a2 == \zero) \/ (∃t. a2 == \next(t))
       : use nat-disj-cases-1;

8.      ∃t. a2 == \next(t)
         : hypothesis a2-next

9.        a2 == \next(w)
           : hypothesis a2-next-w

10.       c1 : chain
           == \plus(\times(a2)(\next(b)))(c2)
            : use reiterate; 6
           == \plus(\times(\next(w))(\next(b)))(c2)
            : hypothesis a2-next-w at z in
              \plus(\times(z)(\next(b)))(c2)
           == \plus(\plus(\next(b))(\times(w)(\next(b))))(c2)
            : use times-next-l; at z in
              \plus(z)(c2)
           == \plus(\next(b))(\plus(\times(w)(\next(b)))(c2))
            : use plus-assoc-r;

11.       ∃h. c1 == \plus(\next(b))(h)
           : exists-intro h <- \plus(\times(w)(\next(b)))(c2); 10

12.       \leq(\next(b))(c1) == \true
           : use plus-impl-leq; 11

13.       \leq(\next(b))(b) == \true
           : use leq-trans; 12, 4

14.     (a2 == \next(w)) => (\leq(\next(b))(b) == \true)
         : discharge a2-next-w; 13

15.     \leq(\next(b))(b) == \true
         : exists-elim w <- t; 8, 14

16.     \true : chain
         == \leq(\next(b))(b)
          : flop use reiterate; 15
         == \false
          : use leq-next-self;

17.   (∃t. a2 == \next(t)) => (\true == \false)
       : discharge a2-next; 16

18.   ~(\true == \false)
       : use bool-disc;

19.   ~(∃t. a2 == \next(t))
       : use modus-tollens; 17, 18

20.   a2 == \zero
       : use disj-syllogism-r; 7, 19

21.   \zero == a2
       : use eq-sym; 20

22.   c1 : chain
       == \plus(\times(a2)(\next(b)))(c2)
        : use reiterate; 6
       == \plus(\times(\zero)(\next(b)))(c2)
        : use reiterate; 20 at z in
          \plus(\times(z)(\next(b)))(c2)
       == \plus(\zero)(c2)
        : use times-zero-l; at z in
          \plus(z)(c2)
       == c2
        : use plus-zero-l;

23.   (\zero == a2) /\ (c1 == c2)
       : use conj-intro; 21, 22

24. ((\plus(\times(\zero)(\next(b)))(c1) == \plus(\times(a2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
      ((\zero == a2) /\ (c1 == c2))
     : discharge zero; 23

25. ∀u2. ((\plus(\times(\zero)(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
      ((\zero == u2) /\ (c1 == c2))
     : forall-intro a2 -> u2; 24

26.   ∀u2. ((\plus(\times(n)(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
          ((n == u2) /\ (c1 == c2))
       : hypothesis n

27.     (\plus(\times(\next(n))(\next(b)))(c1) == \plus(\times(u)(\next(b)))(c2)) /\
          ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))
         : hypothesis next

28.     \plus(\times(\next(n))(\next(b)))(c1) == \plus(\times(u)(\next(b)))(c2)
         : use conj-elim-l; 27

29.     (\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true)
         : use conj-elim-r; 27

30.     \leq(c1)(b) == \true
         : use conj-elim-l; 29

31.     \leq(c2)(b) == \true
         : use conj-elim-r; 29

32.     (u == \zero) \/ (∃t. u == \next(t))
         : use nat-disj-cases-1;

33.       u == \zero
           : hypothesis u-zero

34.       c2 : chain
           == \plus(\zero)(c2)
            : flop use plus-zero-l;
           == \plus(\times(\zero)(\next(b)))(c2)
            : flop use times-zero-l; at z in
              \plus(z)(c2)
           == \plus(\times(u)(\next(b)))(c2)
            : flop hypothesis u-zero at z in
              \plus(\times(z)(\next(b)))(c2)
           == \plus(\times(\next(n))(\next(b)))(c1)
            : flop use reiterate; 28
           == \plus(\plus(\next(b))(\times(n)(\next(b))))(c1)
            : use times-next-l; at z in
              \plus(z)(c1)
           == \plus(\next(b))(\plus(\times(n)(\next(b)))(c1))
            : use plus-assoc-r;

35.       ∃h. c2 == \plus(\next(b))(h)
           : exists-intro h <- \plus(\times(n)(\next(b)))(c1); 34

36.       \leq(\next(b))(c2) == \true
           : use plus-impl-leq; 35

37.       \leq(\next(b))(b) == \true
           : use leq-trans; 36, 31

38.       \true : chain
           == \leq(\next(b))(b)
            : flop use reiterate; 37
           == \false
            : use leq-next-self;

39.     (u == \zero) => (\true == \false)
         : discharge u-zero; 38

40.     ~(\true == \false)
         : use bool-disc;

41.     ~(u == \zero)
         : use modus-tollens; 39, 40

42.     ∃t. u == \next(t)
         : use disj-syllogism-l; 32, 41

43.       u == \next(w)
           : hypothesis u-next-w

44.       \plus(\next(b))(\plus(\times(n)(\next(b)))(c1)) : chain
           == \plus(\plus(\next(b))(\times(n)(\next(b))))(c1)
            : use plus-assoc-l;
           == \plus(\times(\next(n))(\next(b)))(c1)
            : flop use times-next-l; at z in
              \plus(z)(c1)
           == \plus(\times(u)(\next(b)))(c2)
            : use reiterate; 28
           == \plus(\times(\next(w))(\next(b)))(c2)
            : hypothesis u-next-w at z in
              \plus(\times(z)(\next(b)))(c2)
           == \plus(\plus(\next(b))(\times(w)(\next(b))))(c2)
            : use times-next-l; at z in
              \plus(z)(c2)
           == \plus(\next(b))(\plus(\times(w)(\next(b)))(c2))
            : use plus-assoc-r;

45.       \plus(\times(n)(\next(b)))(c1) == \plus(\times(w)(\next(b)))(c2)
           : use plus-cancel-l; 44

46.       ((\plus(\times(n)(\next(b)))(c1) == \plus(\times(w)(\next(b)))(c2)) /\
            ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
              ((n == w) /\ (c1 == c2))
           : forall-elim u2 -> w; 26

47.       ((\plus(\times(n)(\next(b)))(c1) == \plus(\times(w)(\next(b)))(c2)) /\
            ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true)))
           : use conj-intro; 45, 29

48.       (n == w) /\ (c1 == c2)
           : use impl-elim; 47, 46

49.       n == w
           : use conj-elim-l; 48

50.       c1 == c2
           : use conj-elim-r; 48

51.       \next(n) : chain
           == \next(w)
            : use reiterate; 49 at z in \next(z)
           == u
            : flop hypothesis u-next-w

52.       (\next(n) == u) /\ (c1 == c2)
           : use conj-intro; 51, 50

53.     (u == \next(w)) => ((\next(n) == u) /\ (c1 == c2))
         : discharge u-next-w; 52

54.     (\next(n) == u) /\ (c1 == c2)
         : exists-elim w <- t; 42, 53

55.   ((\plus(\times(\next(n))(\next(b)))(c1) == \plus(\times(u)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
          ((\next(n) == u) /\ (c1 == c2))
       : discharge next; 54

56.   ∀u2. ((\plus(\times(\next(n))(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
          ((\next(n) == u2) /\ (c1 == c2))
       : forall-intro u -> u2; 55

57. (∀u2. ((\plus(\times(n)(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
          ((n == u2) /\ (c1 == c2))) =>
      (∀u2. ((\plus(\times(\next(n))(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
          ((\next(n) == u2) /\ (c1 == c2)))
     : discharge n; 56

58. ∀k. ((∀u2. ((\plus(\times(k)(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
          ((k == u2) /\ (c1 == c2))) =>
      (∀u2. ((\plus(\times(\next(k))(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
          ((\next(k) == u2) /\ (c1 == c2))))
     : forall-intro n -> k; 57

59. ∀k. (∀u2. ((\plus(\times(k)(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
        ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
          ((k == u2) /\ (c1 == c2)))
     : invoke nat-induction
       [P :-> (∀u2. ((\plus(\times(_)(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
         ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
           ((_ == u2) /\ (c1 == c2)))]; 25, 58

60. ∀u2. ((\plus(\times(a1)(\next(b)))(c1) == \plus(\times(u2)(\next(b)))(c2)) /\
      ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
        ((a1 == u2) /\ (c1 == c2))
     : forall-elim k -> a1; 59

61. ((\plus(\times(a1)(\next(b)))(c1) == \plus(\times(a2)(\next(b)))(c2)) /\
      ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))) =>
        ((a1 == a2) /\ (c1 == c2))
     : forall-elim u2 -> a2; 60

62. \plus(\times(a1)(\next(b)))(c1) == \plus(\times(a2)(\next(b)))(c2)
     : assumption 1

63. \leq(c1)(b) == \true
     : assumption 2

64. \leq(c2)(b) == \true
     : assumption 3

65. (\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true)
     : use conj-intro; 63, 64

66. (\plus(\times(a1)(\next(b)))(c1) == \plus(\times(a2)(\next(b)))(c2)) /\
      ((\leq(c1)(b) == \true) /\ (\leq(c2)(b) == \true))
     : use conj-intro; 62, 65

67. (a1 == a2) /\ (c1 == c2)
     : use impl-elim; 66, 61
~~~

~~~ {.mycelium}
theorem divalg-unique
if
  * a == \plus(\times(q)(\next(b)))(r)
  * \leq(r)(b) == \true
then
  * \divalg(a)(\next(b)) == \tup(q)(r)

proof
1.  a == \plus(\times(q)(\next(b)))(r)
     : assumption 1

2.  \leq(r)(b) == \true
     : assumption 2

3.  \divalg(a)(\next(b)) == \tup(\quo(a)(\next(b)))(\rem(a)(\next(b)))
     : use divalg-quo-rem;

4.  (a == \plus(\times(\quo(a)(\next(b)))(\next(b)))(\rem(a)(\next(b)))) /\
      (\leq(\rem(a)(\next(b)))(b) == \true)
     : use divalg-exists; 3

5.  a == \plus(\times(\quo(a)(\next(b)))(\next(b)))(\rem(a)(\next(b)))
     : use conj-elim-l; 4

6.  \leq(\rem(a)(\next(b)))(b) == \true
     : use conj-elim-r; 4

7.  \plus(\times(q)(\next(b)))(r) : chain
     == a
      : flop use reiterate; 1
     == \plus(\times(\quo(a)(\next(b)))(\next(b)))(\rem(a)(\next(b)))
      : use reiterate; 5

8.  (q == \quo(a)(\next(b))) /\ (r == \rem(a)(\next(b)))
     : use divalg-unique-lemma; 7, 2, 6

9.  \divalg(a)(\next(b)) : chain
     == \tup(\quo(a)(\next(b)))(\rem(a)(\next(b)))
      : use divalg-quo-rem;
     == \tup(q)(r)
      : flop use tup-eq-2; 8
~~~

~~~ {.mycelium}
theorem divalg-nat-one
* \divalg(a)(\next(\zero)) == \tup(a)(\zero)

proof
1. a : chain
    == \plus(a)(\zero)
     : flop use plus-zero-r;
    == \plus(\times(a)(\next(\zero)))(\zero)
     : flop use times-one-r; at z in
       \plus(z)(\zero)

2. \leq(\zero)(\zero) == \true
    : use leq-refl;

3. \divalg(a)(\next(\zero)) == \tup(a)(\zero)
    : use divalg-unique; 1, 2
~~~

~~~ {.mycelium}
theorem divalg-leq
if
  * \leq(a)(b) == \true
then
  * \divalg(a)(\next(b)) == \tup(\zero)(a)

proof
1. a : chain
    == \plus(\zero)(a)
     : flop use plus-zero-l;
    == \plus(\times(\zero)(\next(b)))(a)
     : flop use times-zero-l; at z in
       \plus(z)(a)

2. \leq(a)(b) == \true
    : assumption 1

3. \divalg(a)(\next(b)) == \tup(\zero)(a)
    : use divalg-unique; 1, 2
~~~

~~~ {.mycelium}
theorem divalg-self-pos
* \divalg(\next(a))(\next(a)) == \tup(\next(\zero))(\zero)

proof
1. \next(a) : chain
    == \plus(\next(a))(\zero)
     : flop use plus-zero-r;
    == \plus(\times(\next(\zero))(\next(a)))(\zero)
     : flop use times-one-l; at z in
       \plus(z)(\zero)

2. \leq(\zero)(a) == \true
    : use leq-zero-l;

3. \divalg(\next(a))(\next(a)) == \tup(\next(\zero))(\zero)
    : use divalg-unique; 1, 2
~~~

~~~ {.mycelium}
theorem divalg-times
* \divalg(\times(a)(\next(b)))(\next(b)) == \tup(a)(\zero)

proof
1. \times(a)(\next(b)) : chain
    == \plus(\times(a)(\next(b)))(\zero)
     : flop use plus-zero-r;

2. \leq(\zero)(b) == \true
    : use leq-zero-l;

3. \divalg(\times(a)(\next(b)))(\next(b)) == \tup(a)(\zero)
    : use divalg-unique; 1, 2
~~~

~~~ {.mycelium}
theorem rem-self
* \rem(a)(a) == \zero

proof
1.  (a == \zero) \/ (∃k. a == \next(k))
     : use nat-disj-cases-1;

2.    a == \zero
       : hypothesis zero

3.    \rem(a)(a) : chain
       == \rem(\zero)(a)
        : hypothesis zero at z in
          \rem(z)(a)
       == \snd(\divalg(\zero)(a))
        : use def-rem;
       == \snd(\tup(\zero)(\zero))
        : use divalg-zero-l; at z in
          \snd(z)
       == \zero
        : use snd-tup;

4.  (a == \zero) =>
      (\rem(a)(a) == \zero)
     : discharge zero; 3

5.    ∃k. a == \next(k)
       : hypothesis next

6.      a == \next(t)
         : hypothesis next-t

7.      \rem(a)(a) : chain
         == \rem(\next(t))(a)
          : hypothesis next-t at z in
            \rem(z)(a)
         == \rem(\next(t))(\next(t))
          : hypothesis next-t at z in
            \rem(\next(t))(z)
         == \snd(\divalg(\next(t))(\next(t)))
          : use def-rem;
         == \snd(\tup(\next(\zero))(\zero))
          : use divalg-self-pos; at z in
            \snd(z)
         == \zero
          : use snd-tup;

8.    (a == \next(t)) =>
        (\rem(a)(a) == \zero)
       : discharge next-t; 7

9.    \rem(a)(a) == \zero
       : exists-elim t <- k; 5, 8

10. (∃k. a == \next(k)) =>
      (\rem(a)(a) == \zero)
     : discharge next; 9

11. \rem(a)(a) == \zero
     : use disj-elim; 1, 4, 10
~~~
