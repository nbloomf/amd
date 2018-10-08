---
title: Iterative Norms
---

~~~ {.mycelium}
definition def-iterative-norm
* (<eta, phi> 'is "iterative-norm") <=>
    ((∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)) /\
      (∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)))
~~~

~~~ {.mycelium}
theorem iterative-norm-zero
if
  * <eta, phi> 'is "iterative-norm"
then
  * ∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)

proof
1. <eta, phi> 'is "iterative-norm"
    : assumption 1

2.  (<eta, phi> 'is "iterative-norm") <=>
      ((∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)) /\
        (∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)))
     : use def-iterative-norm;

3.  (∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)) /\
      (∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true))
     : use equiv-to-l; 2, 1

4.  ∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)
     : use conj-elim-l; 3


theorem iterative-norm-next
if
  * <eta, phi> 'is "iterative-norm"
then
  * ∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)

proof
1. <eta, phi> 'is "iterative-norm"
    : assumption 1

2.  (<eta, phi> 'is "iterative-norm") <=>
      ((∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)) /\
        (∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)))
     : use def-iterative-norm;

3.  (∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)) /\
      (∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true))
     : use equiv-to-l; 2, 1

4.  ∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)
     : use conj-elim-r; 3


theorem is-iterative-norm
if
  * ∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)
  * ∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)
then
  * <eta, phi> 'is "iterative-norm"

proof
1. ∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)
    : assumption 1

2. ∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)
    : assumption 2

3. (∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)) /\
     (∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true))
    : use conj-intro; 1, 2

4.  (<eta, phi> 'is "iterative-norm") <=>
      ((∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)) /\
        (∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)))
     : use def-iterative-norm;

5. <eta, phi> 'is "iterative-norm"
    : use equiv-to-r; 4, 3
~~~

~~~ {.mycelium}
type \normrecW :: (a -> a) -> Nat -> a -> a

definition def-normrecW
* \normrecW(phi)(m)(a) == phi(a)


type \normrecH :: (a -> Nat) -> (a -> b) -> Nat -> a -> b -> b

definition def-normrecH
* \normrecH(eta)(chi)(m)(a)(b) == \if(chi(a))(b)(\eq(\zero)(eta(a)))


type \normrec :: (a -> a) -> (a -> Nat) -> (a -> b) -> a -> b

definition def-normrec
* \normrec(phi)(eta)(chi)(a) ==
    \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(eta(a))(a)
~~~

~~~ {.mycelium}
theorem normrec-lemma
if
  * <eta, phi> 'is "iterative-norm"
then
  * \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
      \plus(eta(phi(a)))(k))(phi(a))
     == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          eta(phi(a)))(phi(a))

proof
1.  <eta, phi> 'is "iterative-norm"
     : assumption 1

2.  (<eta, phi> 'is "iterative-norm") <=>
      ((∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)) /\
        (∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)))
     : use def-iterative-norm;

3.  (∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)) /\
      (∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true))
     : use equiv-to-l; 2, 1

4.  ∀u. (eta(u) == \zero) => (eta(phi(u)) == \zero)
     : use conj-elim-l; 3

5.  ∀u. (eta(u) == \next(n)) => (\leq(eta(phi(u)))(n) == \true)
     : use conj-elim-r; 3

6.    \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(\zero))(phi(a)) : chain
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a))
        : use plus-zero-r; at z in
          \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            z)(phi(a))

7.  (\leq(eta(phi(a)))(\zero) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(\zero))(phi(a))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a)))
     : use simp; 6

8.    (\leq(eta(phi(a)))(\zero) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(a)))(u))(phi(a))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a)))
       : hypothesis u

9.      \leq(eta(phi(a)))(\zero) == \true
         : hypothesis u-next

10.     eta(phi(a)) == \zero
         : use leq-zero-is-zero; 9

11.     \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(a)))(u))(phi(a))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a))
          : use impl-elim; 9, 8

12.     \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          u)(phi(a)) : chain

         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(\zero)(u))(phi(a))
          : flop use plus-zero-l; at z in
            \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              z)(phi(a))

         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(eta(phi(a)))(u))(phi(a))
          : flop use reiterate; 10 at z in
            \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(z)(u))(phi(a))

         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a))
          : use reiterate; 11

13.     \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(a)))(\next(u)))(phi(a)) : chain

         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(\zero)(\next(u)))(phi(a))
          : use reiterate; 10 at z in
            \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(z)(\next(u)))(phi(a))

         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \next(u))(phi(a))
          : use plus-zero-l; at z in
            \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              z)(phi(a))

         == \normrecH(eta)(chi)(u)(phi(a))(
              \mutrec(chi)(\normrecW(phi))(
                \normrecH(eta)(chi))(u)(
                \normrecW(phi)(u)(phi(a))))
          : use mutrec-next;

         == \if(chi(phi(a)))(
              \mutrec(chi)(\normrecW(phi))(
                \normrecH(eta)(chi))(u)(
                \normrecW(phi)(u)(phi(a))))(
              \eq(\zero)(eta(phi(a))))
          : use def-normrecH;

         == \if(chi(phi(a)))(
              \mutrec(chi)(\normrecW(phi))(
                \normrecH(eta)(chi))(u)(
                \normrecW(phi)(u)(phi(a))))(
              \eq(\zero)(\zero))
          : use reiterate; 10 at z in
            \if(chi(phi(a)))(
              \mutrec(chi)(\normrecW(phi))(
                \normrecH(eta)(chi))(u)(
                \normrecW(phi)(u)(phi(a))))(
              \eq(\zero)(z))

         == \if(chi(phi(a)))(
              \mutrec(chi)(\normrecW(phi))(
                \normrecH(eta)(chi))(u)(
                \normrecW(phi)(u)(phi(a))))(
              \true)
          : use eq-refl; at z in
            \if(chi(phi(a)))(
              \mutrec(chi)(\normrecW(phi))(
                \normrecH(eta)(chi))(u)(
                \normrecW(phi)(u)(phi(a))))(
              z)

         == chi(phi(a))
          : use if-true;

         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \zero)(phi(a))
          : flop use mutrec-zero;

         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a))
          : flop use reiterate; 10 at z in
            \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              z)(phi(a))

14.   (\leq(eta(phi(a)))(\zero) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(a)))(\next(u)))(phi(a))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a)))
       : discharge u-next; 13

15. ((\leq(eta(phi(a)))(\zero) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(u))(phi(a))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a)))) =>
      ((\leq(eta(phi(a)))(\zero) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(a)))(\next(u)))(phi(a))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a))))
     : use simp; 14

16. ∀t. ((\leq(eta(phi(a)))(\zero) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(t))(phi(a))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a)))) =>
      ((\leq(eta(phi(a)))(\zero) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(a)))(\next(t)))(phi(a))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a))))
     : forall-intro u -> t; 15

17. ∀t. (\leq(eta(phi(a)))(\zero) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(t))(phi(a))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a)))
     : invoke nat-induction
       [P :-> (\leq(eta(phi(a)))(\zero) == \true) =>
         (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
           \plus(eta(phi(a)))(_))(phi(a))
          == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
               eta(phi(a)))(phi(a)))]; 7, 16

18. ∀x. (∀t. (\leq(eta(phi(x)))(\zero) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(x)))(t))(phi(x))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(x)))(phi(x))))
     : forall-intro a -> x; 17

19.   ∀x. (∀t. (\leq(eta(phi(x)))(n) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(x)))(t))(phi(x))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(x)))(phi(x))))
       : hypothesis n

20.     \leq(eta(phi(a)))(\next(n)) == \true
         : hypothesis next-n

21.     (\leq(eta(phi(a)))(n) == \true) \/
          (\eq(eta(phi(a)))(\next(n)) == \true)
         : use leq-next-cases; 20

22.       \leq(eta(phi(a)))(n) == \true
           : hypothesis leq-n

23.       ∀t. (\leq(eta(phi(a)))(n) == \true) =>
            (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(eta(phi(a)))(t))(phi(a))
             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  eta(phi(a)))(phi(a)))
           : forall-elim x -> a; 19

24.       (\leq(eta(phi(a)))(n) == \true) =>
            (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(eta(phi(a)))(w))(phi(a))
             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  eta(phi(a)))(phi(a)))
            : forall-elim t -> w; 23

25.       \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            \plus(eta(phi(a)))(w))(phi(a))
           == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                eta(phi(a)))(phi(a))
           : use impl-elim; 22, 24

26.     (\leq(eta(phi(a)))(n) == \true) =>
          (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            \plus(eta(phi(a)))(w))(phi(a))
           == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                eta(phi(a)))(phi(a)))
         : discharge leq-n; 25

27.       \eq(eta(phi(a)))(\next(n)) == \true
           : hypothesis eq-n

28.       eta(phi(a)) == \next(n)
           : use eq-dereify; 27

29.       (eta(phi(a)) == \next(n)) =>
            (\leq(eta(phi(phi(a))))(n) == \true)
           : forall-elim u -> phi(a); 5

30.       \leq(eta(phi(phi(a))))(n) == \true
           : use impl-elim; 28, 29

31.       ∃k. n == \plus(eta(phi(phi(a))))(k)
           : use leq-impl-plus; 30

32.         n == \plus(eta(phi(phi(a))))(h)
             : hypothesis h

33.         \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(eta(phi(a)))(\zero))(phi(a)) : chain

             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  eta(phi(a)))(phi(a))
              : use plus-zero-r; at z in
                \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  z)(phi(a))

34.         ∀t. (\leq(eta(phi(phi(a))))(n) == \true) =>
              (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                \plus(eta(phi(phi(a))))(t))(phi(phi(a)))
               == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                    eta(phi(phi(a))))(phi(phi(a))))
                : forall-elim x -> phi(a); 19

35.         (\leq(eta(phi(phi(a))))(n) == \true) =>
              (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                \plus(eta(phi(phi(a))))(\plus(h)(w)))(phi(phi(a)))
               == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                    eta(phi(phi(a))))(phi(phi(a))))
             : forall-elim t -> \plus(h)(w); 34

36.         \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(eta(phi(phi(a))))(\plus(h)(w)))(phi(phi(a)))
             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  eta(phi(phi(a))))(phi(phi(a)))
              : use impl-elim; 30, 35

37.         (\leq(eta(phi(phi(a))))(n) == \true) =>
              (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                \plus(eta(phi(phi(a))))(h))(phi(phi(a)))
               == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                    eta(phi(phi(a))))(phi(phi(a))))
             : forall-elim t -> h; 34

38.         \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(eta(phi(phi(a))))(h))(phi(phi(a)))
             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  eta(phi(phi(a))))(phi(phi(a)))
              : use impl-elim; 30, 37

39.         \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(eta(phi(a)))(w))(phi(a)) : chain

             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  \plus(\next(n))(w))(phi(a))
              : use reiterate; 28 at z in
                \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  \plus(z)(w))(phi(a))

             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  \next(\plus(n)(w)))(phi(a))
              : use plus-next-l; at z in
                \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  z)(phi(a))

             == \normrecH(eta)(chi)(\plus(n)(w))(phi(a))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(\plus(n)(w))(
                    \normrecW(phi)(\plus(n)(w))(phi(a))))
              : use mutrec-next;

             == \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(\plus(n)(w))(
                    \normrecW(phi)(\plus(n)(w))(phi(a))))(
                  \eq(\zero)(eta(phi(a))))
              : use def-normrecH;

             == \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(\plus(n)(w))(
                    \normrecW(phi)(\plus(n)(w))(phi(a))))(
                  \eq(\zero)(\next(n)))
              : use reiterate; 28 at z in
                \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(\plus(n)(w))(
                    \normrecW(phi)(\plus(n)(w))(phi(a))))(
                  \eq(\zero)(z))

             == \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(\plus(n)(w))(
                    \normrecW(phi)(\plus(n)(w))(phi(a))))(
                  \false)
              : use eq-zero-next; at z in
                \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(\plus(n)(w))(
                    \normrecW(phi)(\plus(n)(w))(phi(a))))(
                  z)

             == \mutrec(chi)(\normrecW(phi))(
                  \normrecH(eta)(chi))(\plus(n)(w))(
                  \normrecW(phi)(\plus(n)(w))(phi(a)))
              : use if-false;

             == \mutrec(chi)(\normrecW(phi))(
                  \normrecH(eta)(chi))(\plus(n)(w))(
                  phi(phi(a)))
              : use def-normrecW; at z in
                \mutrec(chi)(\normrecW(phi))(
                  \normrecH(eta)(chi))(\plus(n)(w))(
                  z)

             == \mutrec(chi)(\normrecW(phi))(
                  \normrecH(eta)(chi))(
                    \plus(\plus(eta(phi(phi(a))))(h))(w))(
                  phi(phi(a)))
              : hypothesis h at z in
                \mutrec(chi)(\normrecW(phi))(
                  \normrecH(eta)(chi))(\plus(z)(w))(
                  phi(phi(a)))

             == \mutrec(chi)(\normrecW(phi))(
                  \normrecH(eta)(chi))(
                    \plus(eta(phi(phi(a))))(\plus(h)(w)))(
                  phi(phi(a)))
              : use plus-assoc-r; at z in
                \mutrec(chi)(\normrecW(phi))(
                  \normrecH(eta)(chi))(z)(
                  phi(phi(a)))

             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  eta(phi(phi(a))))(phi(phi(a)))
              : use reiterate; 36

             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  \plus(eta(phi(phi(a))))(h))(phi(phi(a)))
              : flop use reiterate; 38

             == \mutrec(chi)(\normrecW(phi))(
                  \normrecH(eta)(chi))(n)(
                  phi(phi(a)))
              : flop hypothesis h at z in
                \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  z)(phi(phi(a)))

             == \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(n)(
                    phi(phi(a))))(
                  \false)
              : flop use if-false;

             == \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(n)(
                    phi(phi(a))))(
                  \eq(\zero)(\next(n)))
              : flop use eq-zero-next; at z in
                \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(n)(
                    phi(phi(a))))(
                  z)

             == \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(n)(
                    phi(phi(a))))(
                  \eq(\zero)(eta(phi(a))))
              : flop use reiterate; 28 at z in
                \if(chi(phi(a)))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(n)(
                    phi(phi(a))))(
                  \eq(\zero)(z))

             == \normrecH(eta)(chi)(n)(phi(a))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(n)(
                    phi(phi(a))))
              : flop use def-normrecH;

             == \normrecH(eta)(chi)(n)(phi(a))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(n)(
                    \normrecW(phi)(n)(phi(a))))
              : flop use def-normrecW; at z in
                \normrecH(eta)(chi)(n)(phi(a))(
                  \mutrec(chi)(\normrecW(phi))(
                    \normrecH(eta)(chi))(n)(
                    z))

             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  \next(n))(phi(a))
              : flop use mutrec-next;

             == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  eta(phi(a)))(phi(a))
              : flop use reiterate; 28 at z in
                \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  z)(phi(a))

40.       (n == \plus(eta(phi(phi(a))))(h)) =>
            ((\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(eta(phi(a)))(w))(phi(a)))
             == (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  eta(phi(a)))(phi(a))))
           : discharge h; 39

41.       (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              \plus(eta(phi(a)))(w))(phi(a)))
             == (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                  eta(phi(a)))(phi(a)))
           : exists-elim h <- k; 31, 40

42.     (\eq(eta(phi(a)))(\next(n)) == \true) =>
          ((\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            \plus(eta(phi(a)))(w))(phi(a)))
           == (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                eta(phi(a)))(phi(a))))
         : discharge eq-n; 41

43.     \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(a)))(w))(phi(a))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a))
          : use disj-elim; 21, 26, 42

44.   (\leq(eta(phi(a)))(\next(n)) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(a)))(w))(phi(a))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a)))
       : discharge next-n; 43

45.   ∀t. (\leq(eta(phi(a)))(\next(n)) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(a)))(t))(phi(a))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(a)))(phi(a)))
       : forall-intro w -> t; 44

46.   ∀x. (∀t. (\leq(eta(phi(x)))(\next(n)) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(x)))(t))(phi(x))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(x)))(phi(x))))
       : forall-intro a -> x; 45

47. (∀x. (∀t. (\leq(eta(phi(x)))(n) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(x)))(t))(phi(x))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(x)))(phi(x))))) =>
      (∀x. (∀t. (\leq(eta(phi(x)))(\next(n)) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(x)))(t))(phi(x))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(x)))(phi(x)))))
     : discharge n; 46

48. ∀m. (∀x. (∀t. (\leq(eta(phi(x)))(m) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(x)))(t))(phi(x))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(x)))(phi(x))))) =>
      (∀x. (∀t. (\leq(eta(phi(x)))(\next(m)) == \true) =>
        (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \plus(eta(phi(x)))(t))(phi(x))
         == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
              eta(phi(x)))(phi(x)))))
     : forall-intro n -> m; 47

49. ∀m. (∀x. (∀t. (\leq(eta(phi(x)))(m) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(x)))(t))(phi(x))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(x)))(phi(x)))))
     : invoke nat-induction
       [P :-> ∀x. (∀t. (\leq(eta(phi(x)))(_) == \true) =>
         (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
           \plus(eta(phi(x)))(t))(phi(x))
          == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
               eta(phi(x)))(phi(x))))]; 18, 48

50. ∀x. (∀t. (\leq(eta(phi(x)))(u) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(x)))(t))(phi(x))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(x)))(phi(x))))
     : forall-elim m -> u; 49

51. ∀t. (\leq(eta(phi(a)))(u) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(t))(phi(a))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a)))
     : forall-elim x -> a; 50

52. ∀m. (∀t. (\leq(eta(phi(a)))(m) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(t))(phi(a))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a))))
     : forall-intro u -> m; 51

53. ∀t. (\leq(eta(phi(a)))(eta(phi(a))) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(t))(phi(a))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a)))
     : forall-elim m -> eta(phi(a)); 52

54. (\leq(eta(phi(a)))(eta(phi(a))) == \true) =>
      (\mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(k))(phi(a))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a)))
     : forall-elim t -> k; 53

55. \leq(eta(phi(a)))(eta(phi(a))) == \true
     : use leq-refl;

56. \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
        \plus(eta(phi(a)))(k))(phi(a))
       == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
            eta(phi(a)))(phi(a))
     : use impl-elim; 55, 54
~~~

~~~ {.mycelium}
theorem normrec-expand
if
  * <eta, phi> 'is "iterative-norm"
then
  * \normrec(phi)(eta)(chi)(a)
     == \if(
          chi(a))(
          \normrec(phi)(eta)(chi)(phi(a)))(
          \eq(\zero)(eta(a)))

proof
1. <eta, phi> 'is "iterative-norm"
    : assumption 1

2. (eta(a) == \zero) \/ (∃k. eta(a) == \next(k))
    : use nat-disj-cases-1;

3.   eta(a) == \zero
      : hypothesis zero

4.   \normrec(phi)(eta)(chi)(a) : chain

      == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          eta(a))(a)
       : use def-normrec;

      == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          \zero)(a)
       : hypothesis zero at z in
         \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
          z)(a)

      == chi(a)
       : use mutrec-zero;

      == \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
           \true)
       : flop use if-true;

      == \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
           \eq(\zero)(\zero))
       : flop use eq-refl; at z in
         \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
           z)

      == \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
           \eq(\zero)(eta(a)))
       : flop hypothesis zero at z in
         \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
           \eq(\zero)(z))

5. (eta(a) == \zero) =>
     ((\normrec(phi)(eta)(chi)(a))
       == (\if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
            \eq(\zero)(eta(a)))))
    : discharge zero; 4

6.   ∃k. eta(a) == \next(k)
      : hypothesis next

7.     eta(a) == \next(u)
        : hypothesis next-u

8.     ∀w. (eta(w) == \next(u)) =>
         (\leq(eta(phi(w)))(u) == \true)
        : use iterative-norm-next; 1

9.     (eta(a) == \next(u)) =>
         (\leq(eta(phi(a)))(u) == \true)
        : forall-elim w -> a; 8

10.    \leq(eta(phi(a)))(u) == \true
        : use impl-elim; 7, 9

11.    ∃k. u == \plus(eta(phi(a)))(k)
        : use leq-impl-plus; 10

12.      u == \plus(eta(phi(a)))(w)
          : hypothesis u

13.      \normrec(phi)(eta)(chi)(a) : chain

          == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
               eta(a))(a)
           : use def-normrec;

          == \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
               \next(u))(a)
           : use reiterate; 7 at z in
             \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
               z)(a)

          == \normrecH(eta)(chi)(u)(a)(
               \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                 u)(\normrecW(phi)(u)(a)))
           : use mutrec-next;

          == \if(
               chi(a))(
               \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                 u)(\normrecW(phi)(u)(a)))(
               \eq(\zero)(eta(a)))
           : use def-normrecH;

          == \if(
               chi(a))(
               \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                 u)(phi(a)))(
               \eq(\zero)(eta(a)))
           : use def-normrecW; at z in
             \if(
               chi(a))(
               \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                 u)(z))(
               \eq(\zero)(eta(a)))

          == \if(
               chi(a))(
               \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                 \plus(eta(phi(a)))(w))(phi(a)))(
               \eq(\zero)(eta(a)))
           : hypothesis u at z in
             \if(
               chi(a))(
               \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                 z)(phi(a)))(
               \eq(\zero)(eta(a)))

          == \if(
               chi(a))(
               \mutrec(chi)(\normrecW(phi))(\normrecH(eta)(chi))(
                 eta(phi(a)))(phi(a)))(
               \eq(\zero)(eta(a)))
           : use normrec-lemma; 1 at z in
             \if(chi(a))(z)(\eq(\zero)(eta(a)))

          == \if(
               chi(a))(
               \normrec(phi)(eta)(chi)(phi(a)))(
               \eq(\zero)(eta(a)))
           : flop use def-normrec; at z in
             \if(chi(a))(z)(\eq(\zero)(eta(a)))

14.    (u == \plus(eta(phi(a)))(w)) =>
         (\normrec(phi)(eta)(chi)(a)
          == \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
               \eq(\zero)(eta(a))))
        : discharge u; 13

15.    \normrec(phi)(eta)(chi)(a)
        == \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
             \eq(\zero)(eta(a)))
        : exists-elim w <- k; 11, 14

16.  (eta(a) == \next(u)) =>
       (\normrec(phi)(eta)(chi)(a)
        == \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
             \eq(\zero)(eta(a))))
      : discharge next-u; 15

17.   \normrec(phi)(eta)(chi)(a)
        == \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
             \eq(\zero)(eta(a)))
       : exists-elim u <- k; 6, 16

18. (∃k. eta(a) == \next(k)) =>
      (\normrec(phi)(eta)(chi)(a)
        == \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
             \eq(\zero)(eta(a))))
     : discharge next; 17

19. \normrec(phi)(eta)(chi)(a)
     == \if(chi(a))(\normrec(phi)(eta)(chi)(phi(a)))(
          \eq(\zero)(eta(a)))
      : use disj-elim; 2, 5, 18
~~~
