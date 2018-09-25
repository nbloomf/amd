---
title: Max and Min
---

~~~ {.mycelium}
type \max :: Nat -> Nat -> Nat

definition def-max
* \max(a)(b) == \if(b)(a)(\leq(a)(b))


type \min :: Nat -> Nat -> Nat

definition def-min
* \min(a)(b) == \if(a)(b)(\leq(a)(b))
~~~


~~~ {.mycelium}
theorem leq-impl-max
if
  * \leq(a)(b) == \true
then
  * \max(a)(b) == b

proof
1. \max(a)(b) : chain
    == \if(b)(a)(\leq(a)(b))
     : use def-max;
    == \if(b)(a)(\true)
     : assumption 1 at z in
       \if(b)(a)(z)
    == b
     : use if-true;


theorem leq-impl-min
if
  * \leq(a)(b) == \true
then
  * \min(a)(b) == a

proof
1. \min(a)(b) : chain
    == \if(a)(b)(\leq(a)(b))
     : use def-min;
    == \if(a)(b)(\true)
     : assumption 1 at z in
       \if(a)(b)(z)
    == a
     : use if-true;
~~~


~~~ {.mycelium}
theorem max-idemp
* \max(a)(a) == a

proof
1. \max(a)(a) : chain
    == \if(a)(a)(\leq(a)(a))
     : use def-max;
    == \if(a)(a)(\true)
     : use leq-refl; at z in
       \if(a)(a)(z)
    == a
     : use if-true;


theorem min-idemp
* \min(a)(a) == a

proof
1. \min(a)(a) : chain
    == \if(a)(a)(\leq(a)(a))
     : use def-min;
    == \if(a)(a)(\true)
     : use leq-refl; at z in
       \if(a)(a)(z)
    == a
     : use if-true;
~~~

~~~ {.mycelium}
theorem max-zero-l
* \max(\zero)(a) == a

proof
1. \max(\zero)(a) : chain
    == \if(a)(\zero)(\leq(\zero)(a))
     : use def-max;
    == \if(a)(\zero)(\true)
     : use leq-zero-l; at z in
       \if(a)(\zero)(z)
    == a
     : use if-true;


theorem min-zero-l
* \min(\zero)(a) == \zero

proof
1. \min(\zero)(a) : chain
    == \if(\zero)(a)(\leq(\zero)(a))
     : use def-min;
    == \if(\zero)(a)(\true)
     : use leq-zero-l; at z in
       \if(\zero)(a)(z)
    == \zero
     : use if-true;
~~~

~~~ {.mycelium}
theorem max-next-next
* \max(\next(a))(\next(b)) == \next(\max(a)(b))

proof
1. \max(\next(a))(\next(b)) : chain
    == \if(\next(b))(\next(a))(\leq(\next(a))(\next(b)))
     : use def-max;
    == \if(\next(b))(\next(a))(\leq(a)(b))
     : use leq-next-next; at z in
       \if(\next(b))(\next(a))(z)
    == \next(\if(b)(a)(\leq(a)(b)))
     : use if-ap;
    == \next(\max(a)(b))
     : flop use def-max; at z in
       \next(z)


theorem min-next-next
* \min(\next(a))(\next(b)) == \next(\min(a)(b))

proof
1. \min(\next(a))(\next(b)) : chain
    == \if(\next(a))(\next(b))(\leq(\next(a))(\next(b)))
     : use def-min;
    == \if(\next(a))(\next(b))(\leq(a)(b))
     : use leq-next-next; at z in
       \if(\next(a))(\next(b))(z)
    == \next(\if(a)(b)(\leq(a)(b)))
     : use if-ap;
    == \next(\min(a)(b))
     : flop use def-min; at z in
       \next(z)
~~~

~~~ {.mycelium}
theorem max-sym
* \max(a)(b) == \max(b)(a)

proof
1.  (\eq(a)(b) == \true) \/
      ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true))
     : use lt-trichotomy;

2.    \eq(a)(b) == \true : hypothesis eq

3.    \leq(a)(b) == \true : use eq-impl-leq; 2

4.    \eq(b)(a) == \true : use eq-reify-sym; 2

5.    \leq(b)(a) == \true : use eq-impl-leq; 4

6.    \max(a)(b) : chain
       == b : use leq-impl-max; 3
       == a : flop use eq-dereify; 2
       == \max(b)(a) : flop use leq-impl-max; 5

7.  (\eq(a)(b) == \true) =>
      (\max(a)(b) == \max(b)(a))
     : discharge eq; 6

8.    (\lt(a)(b) == \true) \/ (\lt(b)(a) == \true)
       : hypothesis neq

9.      \lt(a)(b) == \true
         : hypothesis lt-ab

10.     \max(a)(b) : chain
         == \if(b)(a)(\leq(a)(b))
          : use def-max;
         == \if(b)(a)(\true)
          : use lt-impl-leq; 9 at z in
            \if(b)(a)(z)
         == b
          : use if-true;
         == \if(a)(b)(\false)
          : flop use if-false;
         == \if(a)(b)(\leq(b)(a))
          : flop use lt-impl-not-leq; 9 at z in
            \if(a)(b)(z)
         == \max(b)(a)
          : flop use def-max;

11.   (\lt(a)(b) == \true) =>
        (\max(a)(b) == \max(b)(a))
       : discharge lt-ab; 10

12.     \lt(b)(a) == \true
         : hypothesis lt-ba

13.     \max(a)(b) : chain
         == \if(b)(a)(\leq(a)(b))
          : use def-max;
         == \if(b)(a)(\false)
          : use lt-impl-not-leq; 12 at z in
            \if(b)(a)(z)
         == a
          : use if-false;
         == \if(a)(b)(\true)
          : flop use if-true;
         == \if(a)(b)(\leq(b)(a))
          : flop use lt-impl-leq; 12 at z in
            \if(a)(b)(z)
         == \max(b)(a)
          : flop use def-max;

14.   (\lt(b)(a) == \true) =>
        (\max(a)(b) == \max(b)(a))
       : discharge lt-ba; 13

15.   \max(a)(b) == \max(b)(a)
       : use disj-elim; 8, 11, 14

16. ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true)) =>
      (\max(a)(b) == \max(b)(a))
     : discharge neq; 15

17. \max(a)(b) == \max(b)(a)
     : use disj-elim; 1, 7, 16
~~~
