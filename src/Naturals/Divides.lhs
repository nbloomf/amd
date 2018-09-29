---
title: Divides
---

~~~ {.mycelium}
type \div :: Nat -> Nat -> Bool

definition def-div
* \div(a)(b) == \eq(\zero)(\rem(b)(a))
~~~

~~~ {.mycelium}
theorem div-zero
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
theorem zero-div
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
        : use zero-div; 3
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
