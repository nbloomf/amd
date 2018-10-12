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
theorem gcd-recur-if
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
     : use gcd-recur-if;

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
          : use gcd-recur-if;

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
theorem gcd-recur
* \gcd(a)(b) == \gcd(b)(\rem(a)(b))

proof
1.  (\eq(\zero)(b) == \true) \/ (\eq(\zero)(b) == \false)
     : use bool-cases;

2.    \eq(\zero)(b) == \true
       : hypothesis t

3.    \zero == b
       : use eq-dereify; 2

4.    \gcd(a)(b) : chain

       == \if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(b))
        : use gcd-recur-if;

       == \if(a)(\gcd(b)(\rem(a)(b)))(\true)
        : hypothesis t at z in
          \if(a)(\gcd(b)(\rem(a)(b)))(z)

       == a
        : use if-true;

       == \rem(a)(\zero)
        : flop use rem-zero-r;

       == \rem(a)(b)
        : use reiterate; 3 at z in
          \rem(a)(z)

       == \gcd(\zero)(\rem(a)(b))
        : flop use gcd-zero-l;

       == \gcd(b)(\rem(a)(b))
        : use reiterate; 3 at z in
          \gcd(z)(\rem(a)(b))

5.  (\eq(\zero)(b) == \true) =>
      (\gcd(a)(b) == \gcd(b)(\rem(a)(b)))
     : discharge t; 4

6.    \eq(\zero)(b) == \false
       : hypothesis f

7.    \gcd(a)(b) : chain

       == \if(a)(\gcd(b)(\rem(a)(b)))(\eq(\zero)(b))
        : use gcd-recur-if;

       == \if(a)(\gcd(b)(\rem(a)(b)))(\false)
        : hypothesis f at z in
          \if(a)(\gcd(b)(\rem(a)(b)))(z)

       == \gcd(b)(\rem(a)(b))
        : use if-false;

8.  (\eq(\zero)(b) == \false) =>
      (\gcd(a)(b) == \gcd(b)(\rem(a)(b)))
     : discharge f; 7

9.  \gcd(a)(b) == \gcd(b)(\rem(a)(b))
     : use disj-elim; 1, 5, 8
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
            : use gcd-recur-if;

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
theorem gcd-div-l
* \div(\gcd(a)(b))(a) == \true

proof
1. (\div(\gcd(a)(b))(a) == \true) /\
     (\div(\gcd(a)(b))(b) == \true)
    : use gcd-div;

2. \div(\gcd(a)(b))(a) == \true
    : use conj-elim-l; 1


theorem gcd-div-r
* \div(\gcd(a)(b))(b) == \true

proof
1. (\div(\gcd(a)(b))(a) == \true) /\
     (\div(\gcd(a)(b))(b) == \true)
    : use gcd-div;

2. \div(\gcd(a)(b))(b) == \true
    : use conj-elim-r; 1
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
              : use gcd-recur-if; at z in
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

~~~ {.mycelium}
theorem gcd-unique
if
  * (\div(m)(a) == \true) /\ (\div(m)(b) == \true)
  * ∀u. ((\div(u)(a) == \true) /\ (\div(u)(b) == \true)) =>
      (\div(u)(m) == \true)
then
  * m == \gcd(a)(b)

proof
1. (\div(\gcd(a)(b))(a) == \true) /\
     (\div(\gcd(a)(b))(b) == \true)
    : use gcd-div;

2. ∀u. ((\div(u)(a) == \true) /\
     (\div(u)(b) == \true)) =>
       (\div(u)(m) == \true)
    : assumption 2

3. ((\div(\gcd(a)(b))(a) == \true) /\
     (\div(\gcd(a)(b))(b) == \true)) =>
       (\div(\gcd(a)(b))(m) == \true)
    : forall-elim u -> \gcd(a)(b); 2

4. \div(\gcd(a)(b))(m) == \true
    : use impl-elim; 1, 3

5. (\div(m)(a) == \true) /\ (\div(m)(b) == \true)
    : assumption 1

6. \div(m)(a) == \true
    : use conj-elim-l; 5

7. \div(m)(b) == \true
    : use conj-elim-r; 5

8. \div(m)(\gcd(a)(b)) == \true
    : use gcd-glb; 6, 7

9. m == \gcd(a)(b)
    : use div-antisym; 8, 4
~~~

~~~ {.mycelium}
theorem gcd-idemp
* \gcd(a)(a) == a

proof
1.  \div(a)(a) == \true
     : use div-refl;

2.  (\div(a)(a) == \true) /\ (\div(a)(a) == \true)
     : use conj-intro; 1, 1

3.    (\div(x)(a) == \true) /\ (\div(x)(a) == \true)
       : hypothesis div

4.    \div(x)(a) == \true
       : use conj-elim-l; 3

5.  ((\div(x)(a) == \true) /\ (\div(x)(a) == \true)) =>
      (\div(x)(a) == \true)
     : discharge div; 4

6.  ∀u. ((\div(u)(a) == \true) /\ (\div(u)(a) == \true)) =>
      (\div(u)(a) == \true)
     : forall-intro x -> u; 5

7.  a == \gcd(a)(a)
     : use gcd-unique; 2, 6

8.  \gcd(a)(a) == a
     : use eq-sym; 7
~~~

~~~ {.mycelium}
theorem gcd-comm
* \gcd(a)(b) == \gcd(b)(a)

proof
1. (\div(\gcd(a)(b))(a) == \true) /\
     (\div(\gcd(a)(b))(b) == \true)
    : use gcd-div;

2. \div(\gcd(a)(b))(a) == \true
    : use conj-elim-l; 1

3. \div(\gcd(a)(b))(b) == \true
    : use conj-elim-r; 1

4. \div(\gcd(a)(b))(\gcd(b)(a)) == \true
    : use gcd-glb; 3, 2

5. (\div(\gcd(b)(a))(b) == \true) /\
     (\div(\gcd(b)(a))(a) == \true)
    : use gcd-div;

6. \div(\gcd(b)(a))(b) == \true
    : use conj-elim-l; 5

7. \div(\gcd(b)(a))(a) == \true
    : use conj-elim-r; 5

8. \div(\gcd(b)(a))(\gcd(a)(b)) == \true
    : use gcd-glb; 7, 6

9. \gcd(a)(b) == \gcd(b)(a)
    : use div-antisym; 4, 8
~~~

~~~ {.mycelium}
theorem gcd-assoc-l
* \gcd(a)(\gcd(b)(c)) == \gcd(\gcd(a)(b))(c)

proof
1.  \div(\gcd(a)(\gcd(b)(c)))(a) == \true
     : use gcd-div-l;

2.  \div(\gcd(a)(\gcd(b)(c)))(\gcd(b)(c)) == \true
     : use gcd-div-r;

3.  \div(\gcd(b)(c))(b) == \true
     : use gcd-div-l;

4.  \div(\gcd(a)(\gcd(b)(c)))(b) == \true
     : use div-trans; 2, 3

5.  \div(\gcd(b)(c))(c) == \true
     : use gcd-div-r;

6.  \div(\gcd(a)(\gcd(b)(c)))(c) == \true
     : use div-trans; 2, 5

7.  \div(\gcd(a)(\gcd(b)(c)))(\gcd(a)(b)) == \true
     : use gcd-glb; 1, 4

8.  \div(\gcd(a)(\gcd(b)(c)))(\gcd(\gcd(a)(b))(c)) == \true
     : use gcd-glb; 7, 6

9.  \div(\gcd(\gcd(a)(b))(c))(c) == \true
     : use gcd-div-r;

10. \div(\gcd(\gcd(a)(b))(c))(\gcd(a)(b)) == \true
     : use gcd-div-l;

11. \div(\gcd(a)(b))(a) == \true
     : use gcd-div-l;

12. \div(\gcd(\gcd(a)(b))(c))(a) == \true
     : use div-trans; 10, 11

13. \div(\gcd(a)(b))(b) == \true
     : use gcd-div-r;

14. \div(\gcd(\gcd(a)(b))(c))(b) == \true
     : use div-trans; 10, 13

15. \div(\gcd(\gcd(a)(b))(c))(\gcd(b)(c)) == \true
     : use gcd-glb; 14, 9

16. \div(\gcd(\gcd(a)(b))(c))(\gcd(a)(\gcd(b)(c))) == \true
     : use gcd-glb; 12, 15

17. \gcd(a)(\gcd(b)(c)) == \gcd(\gcd(a)(b))(c)
     : use div-antisym; 8, 16


theorem gcd-assoc-r
* \gcd(\gcd(a)(b))(c) == \gcd(a)(\gcd(b)(c))

proof
1. \gcd(a)(\gcd(b)(c)) == \gcd(\gcd(a)(b))(c)
    : use gcd-assoc-l;

2. \gcd(\gcd(a)(b))(c) == \gcd(a)(\gcd(b)(c))
    : use eq-sym; 1
~~~

~~~ {.mycelium}
theorem gcd-one-r
* \gcd(a)(\next(\zero)) == \next(\zero)

proof
1.  \div(\next(\zero))(a) == \true
     : use div-one-l;

2.  \div(\next(\zero))(\next(\zero)) == \true
     : use div-refl;

3.  (\div(\next(\zero))(a) == \true) /\
      (\div(\next(\zero))(\next(\zero)) == \true)
     : use conj-intro; 1, 2

4.    (\div(x)(a) == \true) /\ (\div(x)(\next(\zero)) == \true)
       : hypothesis div

5.    \div(x)(\next(\zero)) == \true
       : use conj-elim-r; 4

6.  ((\div(x)(a) == \true) /\ (\div(x)(\next(\zero)) == \true)) =>
      (\div(x)(\next(\zero)) == \true)
     : discharge div; 5

7.  ∀u. ((\div(u)(a) == \true) /\ (\div(u)(\next(\zero)) == \true)) =>
      (\div(u)(\next(\zero)) == \true)
     : forall-intro x -> u; 6

8.  \gcd(a)(\next(\zero)) : chain
     == \next(\zero)
      : flop use gcd-unique; 3, 7


theorem gcd-one-l
* \gcd(\next(\zero))(a) == \next(\zero)

proof
1. \gcd(\next(\zero))(a) : chain
    == \gcd(a)(\next(\zero))
     : use gcd-comm;
    == \next(\zero)
     : use gcd-one-r;
~~~

~~~ {.mycelium}
theorem gcd-is-zero
if
  * \gcd(a)(b) == \zero
then
  * (a == \zero) /\ (b == \zero)

proof
1. \div(\zero)(a) : chain

    == \div(\gcd(a)(b))(a)
     : flop assumption 1 at z in
       \div(z)(a)

    == \true
     : use gcd-div-l;

2. a == \zero
    : use div-zero-l; 1

3. \div(\zero)(b) : chain

    == \div(\gcd(a)(b))(b)
     : flop assumption 1 at z in
       \div(z)(b)

    == \true
     : use gcd-div-r;

4. b == \zero
    : use div-zero-l; 3

5. (a == \zero) /\ (b == \zero)
    : use conj-intro; 2, 4
~~~

~~~ {.mycelium}
theorem gcd-div-impl-l
if
  * \div(a)(b) == \true
then
  * \gcd(a)(b) == a

proof
1. \div(a)(b) == \true
    : assumption 1

2. \rem(b)(a) == \zero
    : use div-rem-zero; 1

3. \gcd(a)(b) : chain
    == \gcd(b)(a)
     : use gcd-comm;
    == \gcd(a)(\rem(b)(a))
     : use gcd-recur;
    == \gcd(a)(\zero)
     : use reiterate; 2 at z in
       \gcd(a)(z)
    == a
     : use gcd-zero-r;


theorem gcd-impl-div-l
if
  * \gcd(a)(b) == a
then
  * \div(a)(b) == \true

proof
1. \div(a)(b) : chain

    == \div(\gcd(a)(b))(b)
     : flop assumption 1 at z in
       \div(z)(b)

    == \true
     : use gcd-div-r;
~~~

~~~ {.mycelium}
theorem gcd-div-compat
if
  * \div(a)(b) == \true
then
  * \div(\gcd(a)(c))(\gcd(b)(c)) == \true

proof
1. \div(a)(b) == \true
    : assumption 1

2. \gcd(a)(b) == a
    : use gcd-div-impl-l; 1

3. \gcd(\gcd(a)(c))(\gcd(b)(c)) : chain

    == \gcd(\gcd(\gcd(a)(c))(b))(c)
     : use gcd-assoc-l;

    == \gcd(\gcd(a)(\gcd(c)(b)))(c)
     : use gcd-assoc-r; at z in
       \gcd(z)(c)

    == \gcd(\gcd(a)(\gcd(b)(c)))(c)
     : use gcd-comm; at z in
       \gcd(\gcd(a)(z))(c)

    == \gcd(\gcd(\gcd(a)(b))(c))(c)
     : use gcd-assoc-l; at z in
       \gcd(z)(c)

    == \gcd(\gcd(a)(b))(\gcd(c)(c))
     : use gcd-assoc-r;

    == \gcd(\gcd(a)(b))(c)
     : use gcd-idemp; at z in
       \gcd(\gcd(a)(b))(z)

    == \gcd(a)(c)
     : use reiterate; 2 at z in
       \gcd(z)(c)

4. \div(\gcd(a)(c))(\gcd(b)(c)) == \true
    : use gcd-impl-div-l; 3
~~~

~~~ {.mycelium}
theorem times-gcd-dist-l
* \times(a)(\gcd(b)(c)) == \gcd(\times(a)(b))(\times(a)(c))

proof
1.  (a == \zero) \/ (∃k. a == \next(k))
     : use nat-disj-cases-1;

2.    a == \zero
       : hypothesis zero

3.    \times(a)(\gcd(b)(c)) : chain

       == \times(\zero)(\gcd(b)(c))
        : hypothesis zero at z in
          \times(z)(\gcd(b)(c))

       == \zero
        : use times-zero-l;

       == \gcd(\zero)(\zero)
        : flop use gcd-zero-l;

       == \gcd(\times(\zero)(b))(\zero)
        : flop use times-zero-l; at z in
          \gcd(z)(\zero)

       == \gcd(\times(\zero)(b))(\times(\zero)(c))
        : flop use times-zero-l; at z in
          \gcd(\times(\zero)(b))(z)

       == \gcd(\times(a)(b))(\times(\zero)(c))
        : flop hypothesis zero at z in
          \gcd(\times(z)(b))(\times(\zero)(c))

       == \gcd(\times(a)(b))(\times(a)(c))
        : flop hypothesis zero at z in
          \gcd(\times(a)(b))(\times(z)(c))

4.  (a == \zero) =>
      (\times(a)(\gcd(b)(c)) == \gcd(\times(a)(b))(\times(a)(c)))
     : discharge zero; 3

5.    ∃k. a == \next(k)
       : hypothesis next

6.      a == \next(u)
         : hypothesis u

7.      \div(\gcd(b)(c))(b) == \true
         : use gcd-div-l;

8.      \div(\times(a)(\gcd(b)(c)))(\times(a)(b)) == \true
         : use div-times-compat-l; 7

9.      \div(\gcd(b)(c))(c) == \true
         : use gcd-div-r;

10.     \div(\times(a)(\gcd(b)(c)))(\times(a)(c)) == \true
         : use div-times-compat-l; 9

11.     \div(\times(a)(\gcd(b)(c)))(\gcd(\times(a)(b))(\times(a)(c))) == \true
         : use gcd-glb; 8, 10

12.     \div(a)(\times(a)(b)) == \true
         : use div-times-l;

13.     \div(a)(\times(a)(c)) == \true
         : use div-times-l;

14.     \div(a)(\gcd(\times(a)(b))(\times(a)(c))) == \true
         : use gcd-glb; 12, 13

15.     ∃k. \gcd(\times(a)(b))(\times(a)(c)) == \times(a)(k)
         : use div-impl-times; 14

16.       \gcd(\times(a)(b))(\times(a)(c)) == \times(a)(w)
           : hypothesis w

17.       \div(\times(\next(u))(w))(\times(\next(u))(b)) : chain

           == \div(\times(a)(w))(\times(\next(u))(b))
            : flop hypothesis u at z in
              \div(\times(z)(w))(\times(\next(u))(b))

           == \div(\times(a)(w))(\times(a)(b))
            : flop hypothesis u at z in
              \div(\times(a)(w))(\times(z)(b))

           == \div(\gcd(\times(a)(b))(\times(a)(c)))(\times(a)(b))
            : flop hypothesis w at z in
              \div(z)(\times(a)(b))

           == \true
            : use gcd-div-l;

18.       \div(w)(b) == \true
           : use div-times-next-cancel-l; 17

19.       \div(\times(\next(u))(w))(\times(\next(u))(c)) : chain

           == \div(\times(a)(w))(\times(\next(u))(c))
            : flop hypothesis u at z in
              \div(\times(z)(w))(\times(\next(u))(c))

           == \div(\times(a)(w))(\times(a)(c))
            : flop hypothesis u at z in
              \div(\times(a)(w))(\times(z)(c))

           == \div(\gcd(\times(a)(b))(\times(a)(c)))(\times(a)(c))
            : flop hypothesis w at z in
              \div(z)(\times(a)(c))

           == \true
            : use gcd-div-r;

20.       \div(w)(c) == \true
           : use div-times-next-cancel-l; 19

21.       \div(w)(\gcd(b)(c)) == \true
           : use gcd-glb; 18, 20

22.       \div(\gcd(\times(a)(b))(\times(a)(c)))(\times(a)(\gcd(b)(c))) : chain

           == \div(\times(a)(w))(\times(a)(\gcd(b)(c)))
            : hypothesis w at z in
              \div(z)(\times(a)(\gcd(b)(c)))

           == \true
            : use div-times-compat-l; 21

23.       \times(a)(\gcd(b)(c)) == \gcd(\times(a)(b))(\times(a)(c))
           : use div-antisym; 11, 22

24.     (\gcd(\times(a)(b))(\times(a)(c)) == \times(a)(w)) =>
          (\times(a)(\gcd(b)(c)) == \gcd(\times(a)(b))(\times(a)(c)))
         : discharge w; 23

25.     \times(a)(\gcd(b)(c)) == \gcd(\times(a)(b))(\times(a)(c))
         : exists-elim w <- k; 15, 24

26.   (a == \next(u)) =>
        (\times(a)(\gcd(b)(c)) == \gcd(\times(a)(b))(\times(a)(c)))
       : discharge u; 25

27.   \times(a)(\gcd(b)(c)) == \gcd(\times(a)(b))(\times(a)(c))
       : exists-elim u <- k; 5, 26

28. (∃k. a == \next(k)) =>
      (\times(a)(\gcd(b)(c)) == \gcd(\times(a)(b))(\times(a)(c)))
     : discharge next; 27

29. \times(a)(\gcd(b)(c)) == \gcd(\times(a)(b))(\times(a)(c))
     : use disj-elim; 1, 4, 28
~~~
