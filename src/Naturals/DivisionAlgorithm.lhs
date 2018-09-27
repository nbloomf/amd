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
* \divalg(\zero)(\next(b)) == \tup(\zero)(\zero)

proof
1. \divalg(\zero)(\next(b)) : chain
    == \flip(\simprec(\const(\tup(\zero)(\zero)))(\divalgH))(\zero)(\next(b))
     : use def-divalg; at f in f(\zero)(\next(b))
    == \simprec(\const(\tup(\zero)(\zero)))(\divalgH)(\next(b))(\zero)
     : use def-flip;
    == \const(\tup(\zero)(\zero))(\next(b))
     : use simprec-zero;
    == \tup(\zero)(\zero)
     : use def-const;
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
