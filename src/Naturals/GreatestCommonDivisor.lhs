---
title: Greatest Common Divisor
---

~~~ {.mycelium}
type \gcdH :: Pair Nat Nat -> Pair Nat Nat

definition def-gcdH
* \gcdH(x)
   == \if(
        x)(
        \tup(\snd(x))(\rem(\fst(x))(\snd(x))))(
        \eq(\zero)(\snd(x)))


theorem gcdH-tup
* \gcdH(\tup(a)(b))
   == \if(
        \tup(a)(b))(
        \tup(b)(\rem(a)(b)))(
        \eq(\zero)(b))

proof
1. \gcdH(\tup(a)(b)) : chain

    == \if(
         \tup(a)(b))(
         \tup(\snd(\tup(a)(b)))(\rem(\fst(\tup(a)(b)))(\snd(\tup(a)(b)))))(
         \eq(\zero)(\snd(\tup(a)(b))))
     : use def-gcdH;

    == \if(
         \tup(a)(b))(
         \tup(b)(\rem(\fst(\tup(a)(b)))(\snd(\tup(a)(b)))))(
         \eq(\zero)(\snd(\tup(a)(b))))
     : use snd-tup; at z in
       \if(
         \tup(a)(b))(
         \tup(z)(\rem(\fst(\tup(a)(b)))(\snd(\tup(a)(b)))))(
         \eq(\zero)(\snd(\tup(a)(b))))

    == \if(
         \tup(a)(b))(
         \tup(b)(\rem(\fst(\tup(a)(b)))(b)))(
         \eq(\zero)(\snd(\tup(a)(b))))
     : use snd-tup; at z in
       \if(
         \tup(a)(b))(
         \tup(b)(\rem(\fst(\tup(a)(b)))(z)))(
         \eq(\zero)(\snd(\tup(a)(b))))

    == \if(
         \tup(a)(b))(
         \tup(b)(\rem(a)(b)))(
         \eq(\zero)(\snd(\tup(a)(b))))
     : use fst-tup; at z in
       \if(
         \tup(a)(b))(
         \tup(b)(\rem(z)(b)))(
         \eq(\zero)(\snd(\tup(a)(b))))

    == \if(
         \tup(a)(b))(
         \tup(b)(\rem(a)(b)))(
         \eq(\zero)(b))
     : use snd-tup; at z in
       \if(
         \tup(a)(b))(
         \tup(b)(\rem(a)(b)))(
         \eq(\zero)(z))
~~~

~~~ {.mycelium}
theorem gcd-norm-helper
* <\snd, \gcdH> 'is "iterative-norm"

proof
1.    \snd(w) == \zero
       : hypothesis zero

2.    \snd(\gcdH(w)) : chain

       == \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            \eq(\zero)(\snd(w))))
        : use def-gcdH; at z in \snd(z)

       == \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            \eq(\zero)(\zero)))
        : hypothesis zero at z in
          \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            \eq(\zero)(z)))

       == \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            \true))
        : use eq-refl; at z in
          \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            z))

       == \snd(w)
        : use if-true; at z in \snd(z)

       == \zero
        : hypothesis zero

3.  (\snd(w) == \zero) => (\snd(\gcdH(w)) == \zero)
     : discharge zero; 2

4.  ∀u. (\snd(u) == \zero) => (\snd(\gcdH(u)) == \zero)
     : forall-intro w -> u; 3

5.    \snd(w) == \next(k)
       : hypothesis next

6.    \snd(\gcdH(w)) : chain

       == \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            \eq(\zero)(\snd(w))))
        : use def-gcdH; at z in \snd(z)

       == \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            \eq(\zero)(\next(k))))
        : hypothesis next at z in
          \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            \eq(\zero)(z)))

       == \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            \false))
        : use eq-zero-next; at z in
          \snd(\if(
            w)(
            \tup(\snd(w))(\rem(\fst(w))(\snd(w))))(
            z))

       == \snd(\tup(\snd(w))(\rem(\fst(w))(\snd(w))))
        : use if-false; at z in \snd(z)

       == \rem(\fst(w))(\snd(w))
        : use snd-tup;

       == \rem(\fst(w))(\next(k))
        : hypothesis next at z in
          \rem(\fst(w))(z)

7.    \leq(\snd(\gcdH(w)))(k) : chain

       == \leq(\rem(\fst(w))(\next(k)))(k)
        : use reiterate; 6 at z in
          \leq(z)(k)

       == \true
        : use divalg-bound;

8.  (\snd(w) == \next(k)) =>
      (\leq(\snd(\gcdH(w)))(k) == \true)
     : discharge next; 7

9.  ∀u. (\snd(u) == \next(k)) =>
      (\leq(\snd(\gcdH(u)))(k) == \true)
     : forall-intro w -> u; 8

10. <\snd, \gcdH> 'is "iterative-norm"
     : use is-iterative-norm; 4, 9
~~~

~~~ {.mycelium}
type \gcd :: Nat -> Nat -> Nat

definition def-gcd
* \gcd(a)(b) == \normrec(\gcdH)(\snd)(\fst)(\tup(a)(b))
~~~

~~~ {.mycelium}
theorem gcd-recur
* \gcd(a)(b) == \if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(b))

proof
1.  <\snd, \gcdH> 'is "iterative-norm"
     : use gcd-norm-helper;

2.  (b == \zero) \/ (∃k. b == \next(k))
     : use nat-disj-cases-1;

3.    b == \zero
       : hypothesis zero

4.    \gcd(a)(b) : chain

       == \normrec(\gcdH)(\snd)(\fst)(\tup(a)(b))
        : use def-gcd;

       == \if(
            \fst(\tup(a)(b)))(
            \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
            \eq(\zero)(\snd(\tup(a)(b))))
        : use normrec-expand; 1

       == \if(a)(
            \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
            \eq(\zero)(\snd(\tup(a)(b))))
        : use fst-tup; at z in
          \if(z)(
            \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
            \eq(\zero)(\snd(\tup(a)(b))))

       == \if(a)(
            \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
            \eq(\zero)(b))
        : use snd-tup; at z in
          \if(a)(
            \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
            \eq(\zero)(z))

       == \if(a)(
            \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
            \eq(\zero)(\zero))
        : hypothesis zero at z in
          \if(a)(
            \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
            \eq(\zero)(z))

       == \if(a)(
            \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
            \true)
        : use eq-refl; at z in
          \if(a)(
            \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
            z)

       == a
        : use if-true;

       == \if(a)(
            \gcd(b)(\rem(a)(b)))(
            \true)
        : flop use if-true;

       == \if(a)(
            \gcd(b)(\rem(a)(b)))(
            \eq(\zero)(\zero))
        : flop use eq-refl; at z in
          \if(a)(
            \gcd(b)(\rem(a)(b)))(
            z)

       == \if(a)(
            \gcd(b)(\rem(a)(b)))(
            \eq(\zero)(b))
        : flop hypothesis zero at z in
          \if(a)(
            \gcd(b)(\rem(a)(b)))(
            \eq(\zero)(z))

5.  (b == \zero) =>
      (\gcd(a)(b) == \if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(b)))
     : discharge zero; 4

6.    ∃k. b == \next(k)
       : hypothesis next

7.      b == \next(u)
         : hypothesis next-u

8.      \gcd(a)(b) : chain

         == \normrec(\gcdH)(\snd)(\fst)(\tup(a)(b))
          : use def-gcd;

         == \if(
              \fst(\tup(a)(b)))(
              \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
              \eq(\zero)(\snd(\tup(a)(b))))
          : use normrec-expand; 1

         == \if(a)(
              \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
              \eq(\zero)(\snd(\tup(a)(b))))
          : use fst-tup; at z in
            \if(z)(
              \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
              \eq(\zero)(\snd(\tup(a)(b))))

         == \if(a)(
              \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
              \eq(\zero)(b))
          : use snd-tup; at z in
            \if(a)(
              \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
              \eq(\zero)(z))

         == \if(a)(
              \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
              \eq(\zero)(\next(u)))
          : hypothesis next-u at z in
            \if(a)(
              \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
              \eq(\zero)(z))

         == \if(a)(
              \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
              \false)
          : use eq-zero-next; at z in
            \if(a)(
              \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b))))(
              z)

         == \normrec(\gcdH)(\snd)(\fst)(\gcdH(\tup(a)(b)))
          : use if-false;

         == \normrec(\gcdH)(\snd)(\fst)(\if(
              \tup(a)(b))(
              \tup(b)(\rem(a)(b)))(
              \eq(\zero)(b)))
          : use gcdH-tup; at z in
            \normrec(\gcdH)(\snd)(\fst)(z)

         == \normrec(\gcdH)(\snd)(\fst)(\if(
              \tup(a)(b))(
              \tup(b)(\rem(a)(b)))(
              \eq(\zero)(\next(u))))
          : hypothesis next-u at z in
            \normrec(\gcdH)(\snd)(\fst)(\if(
              \tup(a)(b))(
              \tup(b)(\rem(a)(b)))(
              \eq(\zero)(z)))

         == \normrec(\gcdH)(\snd)(\fst)(\if(
              \tup(a)(b))(
              \tup(b)(\rem(a)(b)))(
              \false))
          : use eq-zero-next; at z in
            \normrec(\gcdH)(\snd)(\fst)(\if(
              \tup(a)(b))(
              \tup(b)(\rem(a)(b)))(
              z))

         == \normrec(\gcdH)(\snd)(\fst)(\tup(b)(\rem(a)(b)))
          : use if-false; at z in
            \normrec(\gcdH)(\snd)(\fst)(z)

         == \gcd(b)(\rem(a)(b))
          : flop use def-gcd;

         == \if(
              a)(
              \gcd(b)(\rem(a)(b)))(
              \false)
          : flop use if-false;

         == \if(
              a)(
              \gcd(b)(\rem(a)(b)))(
              \eq(\zero)(\next(u)))
          : flop use eq-zero-next; at z in
            \if(
              a)(
              \gcd(b)(\rem(a)(b)))(
              z)

         == \if(
              a)(
              \gcd(b)(\rem(a)(b)))(
              \eq(\zero)(b))
          : flop hypothesis next-u at z in
            \if(
              a)(
              \gcd(b)(\rem(a)(b)))(
              \eq(\zero)(z))

9.    (b == \next(u)) =>
        (\gcd(a)(b) == \if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(b)))
       : discharge next-u; 8

10.   \gcd(a)(b) == \if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(b))
       : exists-elim u <- k; 6, 9

11. (∃k. b == \next(k)) =>
      (\gcd(a)(b) == \if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(b)))
     : discharge next; 10

12. \gcd(a)(b) == \if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(b))
     : use disj-elim; 2, 5, 11
~~~

~~~ {.mycelium}
theorem gcd-zero-r
* \gcd(a)(\zero) == a

proof
1. \gcd(a)(\zero) : chain

    == \if(
         a)(
         \gcd(\zero)(\rem(a)(\zero)))(
         \eq(\zero)(\zero))
     : use gcd-recur;

    == \if(a)(\gcd(\zero)(\rem(a)(\zero)))(\true)
     : use eq-refl; at z in
       \if(a)(\gcd(\zero)(\rem(a)(\zero)))(z)

    == a
     : use if-true;
~~~

~~~ {.mycelium}
theorem gcd-zero-l
* \gcd(\zero)(b) == b

proof
1.  (b == \zero) \/ (∃k. b == \next(k))
     : use nat-disj-cases-1;

2.    b == \zero
       : hypothesis zero

3.    \gcd(\zero)(b) : chain

       == \gcd(\zero)(\zero)
        : hypothesis zero at z in
          \gcd(\zero)(z)

       == \zero
        : use gcd-zero-r;

       == b
        : flop hypothesis zero

4.  (b == \zero) => (\gcd(\zero)(b) == b)
     : discharge zero; 3

5.    ∃k. b == \next(k)
       : hypothesis next

6.      b == \next(t)
         : hypothesis next-t

7.      \gcd(\zero)(b) : chain

         == \gcd(\zero)(\next(t))
          : hypothesis next-t at z in
            \gcd(\zero)(z)

         == \if(
              \zero)(
              \gcd(\next(t))(\rem(\zero)(\next(t))))(
              \eq(\zero)(\next(t)))
          : use gcd-recur;

         == \if(
              \zero)(
              \gcd(\next(t))(\rem(\zero)(\next(t))))(
              \false)
          : use eq-zero-next; at z in
            \if(
              \zero)(
              \gcd(\next(t))(\rem(\zero)(\next(t))))(
              z)

         == \gcd(\next(t))(\rem(\zero)(\next(t)))
          : use if-false;

         == \gcd(\next(t))(\snd(\divalg(\zero)(\next(t))))
          : use def-rem; at z in
            \gcd(\next(t))(z)

         == \gcd(\next(t))(\snd(\tup(\zero)(\zero)))
          : use divalg-zero-l; at z in
            \gcd(\next(t))(\snd(z))

         == \gcd(\next(t))(\zero)
          : use snd-tup; at z in
            \gcd(\next(t))(z)

         == \next(t)
          : use gcd-zero-r;

         == b
          : flop hypothesis next-t

8.    (b == \next(t)) =>
        (\gcd(\zero)(b) == b)
       : discharge next-t; 7

9.    \gcd(\zero)(b) == b
       : exists-elim t <- k; 5, 8

10. (∃k. b == \next(k)) => (\gcd(\zero)(b) == b)
     : discharge next; 9

11. \gcd(\zero)(b) == b
     : use disj-elim; 1, 4, 10
~~~

~~~ {.mycelium}
theorem gcd-div
* (\div(\gcd(a)(b))(a) == \true) /\
    (\div(\gcd(a)(b))(b) == \true)

proof
1.    \leq(b)(\zero) == \true
       : hypothesis zero

2.    b == \zero
       : use leq-zero-is-zero; 1

3.    \div(\gcd(a)(b))(a) : chain

       == \div(\gcd(a)(\zero))(a)
        : use reiterate; 2 at z in
          \div(\gcd(a)(z))(a)

       == \div(a)(a)
        : use gcd-zero-r; at z in
          \div(z)(a)

       == \true
        : use div-refl;

4.    \div(\gcd(a)(b))(b) : chain

       == \div(\gcd(a)(b))(\zero)
        : use reiterate; 2 at z in
          \div(\gcd(a)(b))(z)

       == \true
        : use div-zero-r;

5.    (\div(\gcd(a)(b))(a) == \true) /\
        (\div(\gcd(a)(b))(b) == \true)
       : use conj-intro; 3, 4

6.  (\leq(b)(\zero) == \true) =>
      ((\div(\gcd(a)(b))(a) == \true) /\
        (\div(\gcd(a)(b))(b) == \true))
     : discharge zero; 5

7.  ∀v. (\leq(v)(\zero) == \true) =>
      ((\div(\gcd(a)(v))(a) == \true) /\
        (\div(\gcd(a)(v))(v) == \true))
     : forall-intro b -> v; 6

8.  ∀u. (∀v. (\leq(v)(\zero) == \true) =>
      ((\div(\gcd(u)(v))(u) == \true) /\
        (\div(\gcd(u)(v))(v) == \true)))
     : forall-intro a -> u; 7

9.    ∀u. (∀v. (\leq(v)(n) == \true) =>
        ((\div(\gcd(u)(v))(u) == \true) /\
          (\div(\gcd(u)(v))(v) == \true)))
       : hypothesis n

10.     \leq(b)(\next(n)) == \true
         : hypothesis next

11.     (\leq(b)(n) == \true) \/ (\eq(b)(\next(n)) == \true)
         : use leq-next-cases; 10

12.       \leq(b)(n) == \true
           : hypothesis leq

13.       ∀v. (\leq(v)(n) == \true) =>
            ((\div(\gcd(a)(v))(a) == \true) /\
              (\div(\gcd(a)(v))(v) == \true))
           : forall-elim u -> a; 9

14.       (\leq(b)(n) == \true) =>
            ((\div(\gcd(a)(b))(a) == \true) /\
              (\div(\gcd(a)(b))(b) == \true))
           : forall-elim v -> b; 13

15.       (\div(\gcd(a)(b))(a) == \true) /\
            (\div(\gcd(a)(b))(b) == \true)
           : use impl-elim; 12, 14

16.     (\leq(b)(n) == \true) =>
          ((\div(\gcd(a)(b))(a) == \true) /\
            (\div(\gcd(a)(b))(b) == \true))
         : discharge leq; 15

17.       \eq(b)(\next(n)) == \true
           : hypothesis eq

18.       b == \next(n)
           : use eq-dereify; 17

19.       \gcd(a)(b) : chain

           == \gcd(a)(\next(n))
            : use reiterate; 18 at z in
              \gcd(a)(z)

           == \if(
                a)(
                \gcd(\next(n))(\rem(a)(\next(n))))(
                \eq(\zero)(\next(n)))
            : use gcd-recur;

           == \if(
                a)(
                \gcd(\next(n))(\rem(a)(\next(n))))(
                \false)
            : use eq-zero-next; at z in
              \if(
                a)(
                \gcd(\next(n))(\rem(a)(\next(n))))(
                z)

           == \gcd(\next(n))(\rem(a)(\next(n)))
            : use if-false;

           == \gcd(b)(\rem(a)(\next(n)))
            : flop use reiterate; 18 at z in
              \gcd(z)(\rem(a)(\next(n)))

20.       ∀v. (\leq(v)(n) == \true) =>
            ((\div(\gcd(b)(v))(b) == \true) /\
              (\div(\gcd(b)(v))(v) == \true))
           : forall-elim u -> b; 9

21.       (\leq(\rem(a)(\next(n)))(n) == \true) =>
            ((\div(\gcd(b)(\rem(a)(\next(n))))(b)
             == \true) /\
              (\div(\gcd(b)(\rem(a)(\next(n))))(\rem(a)(\next(n)))
               == \true))
           : forall-elim v -> \rem(a)(\next(n)); 20

22.       \leq(\rem(a)(\next(n)))(n) == \true
           : use divalg-bound;

23.       (\div(\gcd(b)(\rem(a)(\next(n))))(b)
           == \true) /\
            (\div(\gcd(b)(\rem(a)(\next(n))))(\rem(a)(\next(n)))
              == \true)
            : use impl-elim; 22, 21

24.       \div(\gcd(a)(b))(\next(n)) : chain

           == \div(\gcd(a)(b))(b)
            : flop use reiterate; 18 at z in
              \div(\gcd(a)(b))(z)

           == \div(\gcd(b)(\rem(a)(\next(n))))(b)
            : use reiterate; 19 at z in
              \div(z)(b)

           == \true
            : use conj-elim-l; 23

25.       \div(\gcd(a)(b))(\times(\quo(a)(\next(n)))(\next(n)))
           == \true
            : use div-times-absorb-r; 24

26.       \div(\gcd(a)(b))(\rem(a)(\next(n))) : chain

           == \div(\gcd(b)(\rem(a)(\next(n))))(\rem(a)(\next(n)))
            : use reiterate; 19 at z in
              \div(z)(\rem(a)(\next(n)))

           == \true
            : use conj-elim-r; 23

27.       \div(\gcd(a)(b))(a) : chain

           == \div(\gcd(a)(b))(
                \plus(
                  \times(\quo(a)(\next(n)))(\next(n)))(
                  \rem(a)(\next(n))))
            : use divalg-decomp; at z in
              \div(\gcd(a)(b))(z)

           == \true
            : use div-plus-compat; 25, 26

28.       \div(\gcd(a)(b))(b) : chain

           == \div(\gcd(a)(b))(\next(n))
            : use reiterate; 18 at z in
              \div(\gcd(a)(b))(z)

           == \true
            : use reiterate; 24

29.       (\div(\gcd(a)(b))(a) == \true) /\
            (\div(\gcd(a)(b))(b) == \true)
           : use conj-intro; 27, 28

30.     (\eq(b)(\next(n)) == \true) =>
          ((\div(\gcd(a)(b))(a) == \true) /\
            (\div(\gcd(a)(b))(b) == \true))
         : discharge eq; 29

31.     (\div(\gcd(a)(b))(a) == \true) /\
          (\div(\gcd(a)(b))(b) == \true)
         : use disj-elim; 11, 16, 30

32.   (\leq(b)(\next(n)) == \true) =>
        ((\div(\gcd(a)(b))(a) == \true) /\
          (\div(\gcd(a)(b))(b) == \true))
       : discharge next; 31

33.   ∀v. (\leq(v)(\next(n)) == \true) =>
        ((\div(\gcd(a)(v))(a) == \true) /\
          (\div(\gcd(a)(v))(v) == \true))
       : forall-intro b -> v; 32

34.   ∀u. (∀v. (\leq(v)(\next(n)) == \true) =>
        ((\div(\gcd(u)(v))(u) == \true) /\
          (\div(\gcd(u)(v))(v) == \true)))
       : forall-intro a -> u; 33

35. (∀u. (∀v. (\leq(v)(n) == \true) =>
      ((\div(\gcd(u)(v))(u) == \true) /\
        (\div(\gcd(u)(v))(v) == \true)))) =>
      (∀u. (∀v. (\leq(v)(\next(n)) == \true) =>
        ((\div(\gcd(u)(v))(u) == \true) /\
          (\div(\gcd(u)(v))(v) == \true))))
     : discharge n; 34

36. ∀k. ((∀u. (∀v. (\leq(v)(k) == \true) =>
      ((\div(\gcd(u)(v))(u) == \true) /\
        (\div(\gcd(u)(v))(v) == \true)))) =>
      (∀u. (∀v. (\leq(v)(\next(k)) == \true) =>
        ((\div(\gcd(u)(v))(u) == \true) /\
          (\div(\gcd(u)(v))(v) == \true)))))
     : forall-intro n -> k; 35

37. ∀k. (∀u. (∀v. (\leq(v)(k) == \true) =>
      ((\div(\gcd(u)(v))(u) == \true) /\
        (\div(\gcd(u)(v))(v) == \true))))
     : invoke nat-induction
       [P :-> ∀u. (∀v. (\leq(v)(_) == \true) =>
                ((\div(\gcd(u)(v))(u) == \true) /\
                  (\div(\gcd(u)(v))(v) == \true)))]; 8, 36

38. ∀u. (∀v. (\leq(v)(n) == \true) =>
      ((\div(\gcd(u)(v))(u) == \true) /\
        (\div(\gcd(u)(v))(v) == \true)))
     : forall-elim k -> n; 37

39. ∀v. (\leq(v)(n) == \true) =>
      ((\div(\gcd(a)(v))(a) == \true) /\
        (\div(\gcd(a)(v))(v) == \true))
     : forall-elim u -> a; 38

40. (\leq(b)(n) == \true) =>
      ((\div(\gcd(a)(b))(a) == \true) /\
        (\div(\gcd(a)(b))(b) == \true))
     : forall-elim v -> b; 39

41. ∀k. (\leq(b)(k) == \true) =>
      ((\div(\gcd(a)(b))(a) == \true) /\
        (\div(\gcd(a)(b))(b) == \true))
     : forall-intro n -> k; 40

42. (\leq(b)(b) == \true) =>
      ((\div(\gcd(a)(b))(a) == \true) /\
        (\div(\gcd(a)(b))(b) == \true))
     : forall-elim k -> b; 41

43. \leq(b)(b) == \true
     : use leq-refl;

44. (\div(\gcd(a)(b))(a) == \true) /\
      (\div(\gcd(a)(b))(b) == \true)
     : use impl-elim; 43, 42
~~~

~~~ {.mycelium}
theorem gcd-glb
if
  * \div(c)(a) == \true
  * \div(c)(b) == \true
then
  * \div(c)(\gcd(a)(b)) == \true

proof
1.    \leq(b)(\zero) == \true
       : hypothesis zero

2.    b == \zero
       : use leq-zero-is-zero; 1

3.      (\div(c)(a) == \true) /\ (\div(c)(b) == \true)
         : hypothesis zero-div

4.      \div(c)(\gcd(a)(b)) : chain

         == \div(c)(\gcd(a)(\zero))
          : use reiterate; 2 at z in
            \div(c)(\gcd(a)(z))

         == \div(c)(a)
          : use gcd-zero-r; at z in
            \div(c)(z)

         == \true
          : use conj-elim-l; 3

5.    ((\div(c)(a) == \true) /\ (\div(c)(b) == \true)) =>
        (\div(c)(\gcd(a)(b)) == \true)
       : discharge zero-div; 4

6.    ∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
        (\div(c)(\gcd(u)(b)) == \true)
       : forall-intro a -> u; 5

7.  (\leq(b)(\zero) == \true) =>
      (∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
        (\div(c)(\gcd(u)(b)) == \true))
     : discharge zero; 6

8.  ∀v. (\leq(v)(\zero) == \true) =>
      (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
        (\div(c)(\gcd(u)(v)) == \true))
     : forall-intro b -> u; 7

9.    ∀v. (\leq(v)(n) == \true) =>
        (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
          (\div(c)(\gcd(u)(v)) == \true))
       : hypothesis n

10.     \leq(b)(\next(n)) == \true
         : hypothesis next

11.     (\leq(b)(n) == \true) \/ (\eq(b)(\next(n)) == \true)
         : use leq-next-cases; 10

12.       \leq(b)(n) == \true
           : hypothesis leq-n

13.       (\leq(b)(n) == \true) =>
            (∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
              (\div(c)(\gcd(u)(b)) == \true))
           : forall-elim v -> b; 9

14.       ∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
            (\div(c)(\gcd(u)(b)) == \true)
           : use impl-elim; 12, 13

15.     (\leq(b)(n) == \true) =>
          (∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
            (\div(c)(\gcd(u)(b)) == \true))
         : discharge leq-n; 14

16.       \eq(b)(\next(n)) == \true
           : hypothesis eq-next

17.         (\div(c)(a) == \true) /\ (\div(c)(b) == \true)
             : hypothesis conj

18.         \div(c)(\next(n)) : chain
             == \div(c)(b)
              : flop use eq-dereify; 16 at z in
                \div(c)(z)
             == \true
              : use conj-elim-r; 17

19.         \div(c)(\times(\quo(a)(\next(n)))(\next(n)))
             == \true
              : use div-times-absorb-r; 18

20.         \div(c)(\plus(\times(\quo(a)(\next(n)))(\next(n)))(\rem(a)(\next(n)))) : chain

             == \div(c)(a)
              : flop use divalg-decomp; at z in
                \div(c)(z)

             == \true
              : use conj-elim-l; 17

21.         \div(c)(\rem(a)(\next(n))) == \true
             : use div-plus-impl-l; 19, 20

22.         \div(c)(b) == \true
             : use conj-elim-r; 17

23.         \leq(\rem(a)(\next(n)))(n) == \true
             : use divalg-bound;

24.         (\leq(\rem(a)(\next(n)))(n) == \true) =>
              (∀u. ((\div(c)(u) == \true) /\ (\div(c)(\rem(a)(\next(n))) == \true)) =>
                (\div(c)(\gcd(u)(\rem(a)(\next(n)))) == \true))
             : forall-elim v -> \rem(a)(\next(n)); 9

25.         ∀u. ((\div(c)(u) == \true) /\ (\div(c)(\rem(a)(\next(n))) == \true)) =>
              (\div(c)(\gcd(u)(\rem(a)(\next(n)))) == \true)
             : use impl-elim; 23, 24

26.         ((\div(c)(b) == \true) /\ (\div(c)(\rem(a)(\next(n))) == \true)) =>
              (\div(c)(\gcd(b)(\rem(a)(\next(n)))) == \true)
             : forall-elim u -> b; 25

27.         (\div(c)(b) == \true) /\ (\div(c)(\rem(a)(\next(n))) == \true)
             : use conj-intro; 22, 21

28.         \div(c)(\gcd(b)(\rem(a)(\next(n)))) == \true
             : use impl-elim; 27, 26

29.         \div(c)(\gcd(a)(b)) : chain

             == \div(c)(\if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(b)))
              : use gcd-recur; at z in
                \div(c)(z)

             == \div(c)(\if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(\next(n))))
              : use eq-dereify; 16 at z in
                \div(c)(\if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(z)))

             == \div(c)(\if(a)(\gcd(b)(\rem(a)(b)))(\false))
              : use eq-zero-next; at z in
                \div(c)(\if(a)(\gcd(b)(\rem(a)(b)))(z))

             == \div(c)(\gcd(b)(\rem(a)(b)))
              : use if-false; at z in
                \div(c)(z)

             == \div(c)(\gcd(b)(\rem(a)(\next(n))))
              : use eq-dereify; 16 at z in
                \div(c)(\gcd(b)(\rem(a)(z)))

             == \true
              : use reiterate; 28

30.       ((\div(c)(a) == \true) /\ (\div(c)(b) == \true)) =>
            (\div(c)(\gcd(a)(b)) == \true)
           : discharge conj; 29

31.       ∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
            (\div(c)(\gcd(u)(b)) == \true)
           : forall-intro a -> u; 30

32.     (\eq(b)(\next(n)) == \true) =>
          (∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
            (\div(c)(\gcd(u)(b)) == \true))
         : discharge eq-next; 31

33.     ∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
          (\div(c)(\gcd(u)(b)) == \true)
         : use disj-elim; 11, 15, 32

34.   (\leq(b)(\next(n)) == \true) =>
        (∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
          (\div(c)(\gcd(u)(b)) == \true))
       : discharge next; 33

35.   ∀v. ((\leq(v)(\next(n)) == \true) =>
        (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
          (\div(c)(\gcd(u)(v)) == \true)))
       : forall-intro b -> v; 34

36. (∀v. (\leq(v)(n) == \true) =>
      (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
        (\div(c)(\gcd(u)(v)) == \true))) =>
      (∀v. ((\leq(v)(\next(n)) == \true) =>
        (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
          (\div(c)(\gcd(u)(v)) == \true))))
     : discharge n; 35

37. ∀k. (∀v. (\leq(v)(k) == \true) =>
      (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
        (\div(c)(\gcd(u)(v)) == \true))) =>
      (∀v. ((\leq(v)(\next(k)) == \true) =>
        (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
          (\div(c)(\gcd(u)(v)) == \true))))
     : forall-intro n -> k; 36

38. ∀k. (∀v. (\leq(v)(k) == \true) =>
      (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
        (\div(c)(\gcd(u)(v)) == \true)))
     : invoke nat-induction
       [P :-> ∀v. (\leq(v)(_) == \true) =>
                (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
                  (\div(c)(\gcd(u)(v)) == \true))]; 8, 37

39. ∀v. (\leq(v)(b) == \true) =>
      (∀u. ((\div(c)(u) == \true) /\ (\div(c)(v) == \true)) =>
        (\div(c)(\gcd(u)(v)) == \true))
     : forall-elim k -> b; 38

40. (\leq(b)(b) == \true) =>
      (∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
        (\div(c)(\gcd(u)(b)) == \true))
     : forall-elim v -> b; 39

41. \leq(b)(b) == \true
     : use leq-refl;

42. ∀u. ((\div(c)(u) == \true) /\ (\div(c)(b) == \true)) =>
      (\div(c)(\gcd(u)(b)) == \true)
     : use impl-elim; 41, 40

43. ((\div(c)(a) == \true) /\ (\div(c)(b) == \true)) =>
      (\div(c)(\gcd(a)(b)) == \true)
     : forall-elim u -> a; 42

44. \div(c)(a) == \true
     : assumption 1

45. \div(c)(b) == \true
     : assumption 2

46. (\div(c)(a) == \true) /\ (\div(c)(b) == \true)
     : use conj-intro; 44, 45

47. \div(c)(\gcd(a)(b)) == \true
     : use impl-elim; 46, 43
~~~
