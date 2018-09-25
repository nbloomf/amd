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

~~~ {.mycelium}
theorem leq-not-impl-max
if
  * \leq(a)(b) == \false
then
  * \max(a)(b) == a

proof
1. \leq(a)(b) == \false : assumption 1
2. \leq(b)(a) == \true : use leq-false-flip; 1
3. \max(a)(b) : chain
    == \max(b)(a) : use max-sym;
    == a : use leq-impl-max; 2
~~~

~~~ {.mycelium}
theorem min-sym
* \min(a)(b) == \min(b)(a)

proof
1.  (\eq(a)(b) == \true) \/
      ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true))
     : use lt-trichotomy;

2.    \eq(a)(b) == \true : hypothesis eq

3.    \leq(a)(b) == \true : use eq-impl-leq; 2

4.    \eq(b)(a) == \true : use eq-reify-sym; 2

5.    \leq(b)(a) == \true : use eq-impl-leq; 4

6.    \min(a)(b) : chain
       == a : use leq-impl-min; 3
       == b : use eq-dereify; 2
       == \min(b)(a) : flop use leq-impl-min; 5

7.  (\eq(a)(b) == \true) =>
      (\min(a)(b) == \min(b)(a))
     : discharge eq; 6

8.    (\lt(a)(b) == \true) \/ (\lt(b)(a) == \true)
       : hypothesis neq

9.      \lt(a)(b) == \true
         : hypothesis lt-ab

10.     \min(a)(b) : chain
         == \if(a)(b)(\leq(a)(b))
          : use def-min;
         == \if(a)(b)(\true)
          : use lt-impl-leq; 9 at z in
            \if(a)(b)(z)
         == a
          : use if-true;
         == \if(b)(a)(\false)
          : flop use if-false;
         == \if(b)(a)(\leq(b)(a))
          : flop use lt-impl-not-leq; 9 at z in
            \if(b)(a)(z)
         == \min(b)(a)
          : flop use def-min;

11.   (\lt(a)(b) == \true) =>
        (\min(a)(b) == \min(b)(a))
       : discharge lt-ab; 10

12.     \lt(b)(a) == \true
         : hypothesis lt-ba

13.     \min(a)(b) : chain
         == \if(a)(b)(\leq(a)(b))
          : use def-min;
         == \if(a)(b)(\false)
          : use lt-impl-not-leq; 12 at z in
            \if(a)(b)(z)
         == b
          : use if-false;
         == \if(b)(a)(\true)
          : flop use if-true;
         == \if(b)(a)(\leq(b)(a))
          : flop use lt-impl-leq; 12 at z in
            \if(b)(a)(z)
         == \min(b)(a)
          : flop use def-min;

14.   (\lt(b)(a) == \true) =>
        (\min(a)(b) == \min(b)(a))
       : discharge lt-ba; 13

15.   \min(a)(b) == \min(b)(a)
       : use disj-elim; 8, 11, 14

16. ((\lt(a)(b) == \true) \/ (\lt(b)(a) == \true)) =>
      (\min(a)(b) == \min(b)(a))
     : discharge neq; 15

17. \min(a)(b) == \min(b)(a)
     : use disj-elim; 1, 7, 16
~~~

~~~ {.mycelium}
theorem leq-not-impl-min
if
  * \leq(a)(b) == \false
then
  * \min(a)(b) == b

proof
1. \leq(a)(b) == \false : assumption 1
2. \leq(b)(a) == \true : use leq-false-flip; 1
3. \min(a)(b) : chain
    == \min(b)(a) : use min-sym;
    == b : use leq-impl-min; 2
~~~

~~~ {.mycelium}
theorem leq-max-l
* \leq(a)(\max(a)(b)) == \true

proof
1.  (\leq(a)(b) == \true) \/ (\leq(a)(b) == \false)
     : use bool-cases;
2.    \leq(a)(b) == \true : hypothesis t
3.    \leq(a)(\max(a)(b)) : chain
       == \leq(a)(b)
        : use leq-impl-max; 2 at z in
          \leq(a)(z)
       == \true
        : hypothesis t
4.  (\leq(a)(b) == \true) =>
      (\leq(a)(\max(a)(b)) == \true)
     : discharge t; 3
5.    \leq(a)(b) == \false : hypothesis f
6.    \leq(a)(\max(a)(b)) : chain
       == \leq(a)(a)
        : use leq-not-impl-max; 5 at z in
          \leq(a)(z)
       == \true
        : use leq-refl;
7.  (\leq(a)(b) == \false) =>
      (\leq(a)(\max(a)(b)) == \true)
     : discharge f; 6
8.  \leq(a)(\max(a)(b)) == \true
     : use disj-elim; 1, 4, 7


theorem leq-max-r
* \leq(b)(\max(a)(b)) == \true

proof
1. \leq(b)(\max(a)(b)) : chain
    == \leq(b)(\max(b)(a))
     : use max-sym; at z in
       \leq(b)(z)
    == \true
     : use leq-max-l;
~~~

~~~ {.mycelium}
theorem leq-min-l
* \leq(\min(a)(b))(a) == \true

proof
1.  (\leq(a)(b) == \true) \/ (\leq(a)(b) == \false)
     : use bool-cases;
2.    \leq(a)(b) == \true : hypothesis t
3.    \leq(\min(a)(b))(a) : chain
       == \leq(a)(a)
        : use leq-impl-min; 2 at z in
          \leq(z)(a)
       == \true
        : use leq-refl;
4.  (\leq(a)(b) == \true) =>
      (\leq(\min(a)(b))(a) == \true)
     : discharge t; 3
5.    \leq(a)(b) == \false : hypothesis f
6.    \leq(\min(a)(b))(a) : chain
       == \leq(b)(a)
        : use leq-not-impl-min; 5 at z in
          \leq(z)(a)
       == \true
        : use leq-false-flip; 5
7.  (\leq(a)(b) == \false) =>
      (\leq(\min(a)(b))(a) == \true)
     : discharge f; 6
8.  \leq(\min(a)(b))(a) == \true
     : use disj-elim; 1, 4, 7


theorem leq-min-r
* \leq(\min(a)(b))(b) == \true

proof
1. \leq(\min(a)(b))(b) : chain
    == \leq(\min(b)(a))(b)
     : use min-sym; at z in
       \leq(z)(b)
    == \true
     : use leq-min-l;
~~~

~~~ {.mycelium}
theorem max-cases
* (\max(a)(b) == a) \/ (\max(a)(b) == b)

proof
1.  (\leq(a)(b) == \true) \/ (\leq(a)(b) == \false)
     : use bool-cases;
2.    \leq(a)(b) == \true : hypothesis t
3.    \max(a)(b) == b : use leq-impl-max; 2
4.    (\max(a)(b) == a) \/ (\max(a)(b) == b)
       : use disj-intro-r; 3
5.  (\leq(a)(b) == \true) =>
      ((\max(a)(b) == a) \/ (\max(a)(b) == b))
     : discharge t; 4
6.    \leq(a)(b) == \false : hypothesis f
7.    \max(a)(b) == a : use leq-not-impl-max; 6
8.    (\max(a)(b) == a) \/ (\max(a)(b) == b)
       : use disj-intro-l; 7
9.  (\leq(a)(b) == \false) =>
      ((\max(a)(b) == a) \/ (\max(a)(b) == b))
     : discharge f; 8
10. (\max(a)(b) == a) \/ (\max(a)(b) == b)
     : use disj-elim; 1, 5, 9


theorem min-cases
* (\min(a)(b) == a) \/ (\min(a)(b) == b)

proof
1.  (\leq(a)(b) == \true) \/ (\leq(a)(b) == \false)
     : use bool-cases;
2.    \leq(a)(b) == \true : hypothesis t
3.    \min(a)(b) == a : use leq-impl-min; 2
4.    (\min(a)(b) == a) \/ (\min(a)(b) == b)
       : use disj-intro-l; 3
5.  (\leq(a)(b) == \true) =>
      ((\min(a)(b) == a) \/ (\min(a)(b) == b))
     : discharge t; 4
6.    \leq(a)(b) == \false : hypothesis f
7.    \min(a)(b) == b : use leq-not-impl-min; 6
8.    (\min(a)(b) == a) \/ (\min(a)(b) == b)
       : use disj-intro-r; 7
9.  (\leq(a)(b) == \false) =>
      ((\min(a)(b) == a) \/ (\min(a)(b) == b))
     : discharge f; 8
10. (\min(a)(b) == a) \/ (\min(a)(b) == b)
     : use disj-elim; 1, 5, 9
~~~

~~~ {.mycelium}
theorem max-glb
if
  * \leq(a)(c) == \true
  * \leq(b)(c) == \true
then
  * \leq(\max(a)(b))(c) == \true

proof
1. (\max(a)(b) == a) \/ (\max(a)(b) == b)
    : use max-cases;
2.   \max(a)(b) == a : hypothesis a
3.   \leq(\max(a)(b))(c) : chain
      == \leq(a)(c)
       : hypothesis a at z in
         \leq(z)(c)
      == \true
       : assumption 1
4. (\max(a)(b) == a) => (\leq(\max(a)(b))(c) == \true)
    : discharge a; 3
5.   \max(a)(b) == b : hypothesis b
6.   \leq(\max(a)(b))(c) : chain
      == \leq(b)(c)
       : hypothesis b at z in
         \leq(z)(c)
      == \true
       : assumption 2
7. (\max(a)(b) == b) => (\leq(\max(a)(b))(c) == \true)
    : discharge b; 6
8. \leq(\max(a)(b))(c) == \true
    : use disj-elim; 1, 4, 7
~~~

~~~ {.mycelium}
theorem leq-leq-max
if
  * \leq(a)(b) == \true
then
  * \leq(a)(\max(b)(c)) == \true

proof
1. \leq(a)(b) == \true : assumption 1
2. \leq(b)(\max(b)(c)) == \true : use leq-max-l;
3. \leq(a)(\max(b)(c)) == \true : use leq-trans; 1, 2


theorem leq-leq-min
if
  * \leq(a)(b) == \true
then
  * \leq(\min(a)(c))(b) == \true

proof
1. \leq(a)(b) == \true : assumption 1
2. \leq(\min(a)(c))(a) == \true : use leq-min-l;
3. \leq(\min(a)(c))(b) == \true : use leq-trans; 2, 1
~~~

~~~ {.mycelium}
theorem min-lub
if
  * \leq(c)(a) == \true
  * \leq(c)(b) == \true
then
  * \leq(c)(\min(a)(b)) == \true

proof
1. (\min(a)(b) == a) \/ (\min(a)(b) == b)
    : use min-cases;
2.   \min(a)(b) == a : hypothesis a
3.   \leq(c)(\min(a)(b)) : chain
      == \leq(c)(a)
       : hypothesis a at z in
         \leq(c)(z)
      == \true
       : assumption 1
4. (\min(a)(b) == a) => (\leq(c)(\min(a)(b)) == \true)
    : discharge a; 3
5.   \min(a)(b) == b : hypothesis b
6.   \leq(c)(\min(a)(b)) : chain
      == \leq(c)(b)
       : hypothesis b at z in
         \leq(c)(z)
      == \true
       : assumption 2
7. (\min(a)(b) == b) => (\leq(c)(\min(a)(b)) == \true)
    : discharge b; 6
8. \leq(c)(\min(a)(b)) == \true
    : use disj-elim; 1, 4, 7
~~~

~~~ {.mycelium}
theorem max-assoc-l
* \max(a)(\max(b)(c)) == \max(\max(a)(b))(c)

proof
1.  \leq(a)(\max(a)(b)) == \true
     : use leq-max-l;
2.  \leq(a)(\max(\max(a)(b))(c)) == \true
     : use leq-leq-max; 1
3.  \leq(b)(\max(a)(b)) == \true
     : use leq-max-r;
4.  \leq(b)(\max(\max(a)(b))(c)) == \true
     : use leq-leq-max; 3
5.  \leq(c)(\max(\max(a)(b))(c)) == \true
     : use leq-max-r;
6.  \leq(\max(b)(c))(\max(\max(a)(b))(c)) == \true
     : use max-glb; 4, 5
7.  \leq(\max(a)(\max(b)(c)))(\max(\max(a)(b))(c)) == \true
     : use max-glb; 2, 6
8.  \leq(a)(\max(a)(\max(b)(c))) == \true
     : use leq-max-l;
9.  \leq(b)(\max(b)(c)) == \true
     : use leq-max-l;
10. \leq(b)(\max(a)(\max(b)(c))) : chain
     == \leq(b)(\max(\max(b)(c))(a))
      : use max-sym; at z in
        \leq(b)(z)
     == \true
      : use leq-leq-max; 9
11. \leq(\max(a)(b))(\max(a)(\max(b)(c))) == \true
     : use max-glb; 8, 10
12. \leq(c)(\max(b)(c)) == \true
     : use leq-max-r;
13. \leq(c)(\max(a)(\max(b)(c))) : chain
     == \leq(c)(\max(\max(b)(c))(a))
      : use max-sym; at z in
        \leq(c)(z)
     == \true
      : use leq-leq-max; 12
14. \leq(\max(\max(a)(b))(c))(\max(a)(\max(b)(c))) == \true
     : use max-glb; 11, 13
15. \max(a)(\max(b)(c)) == \max(\max(a)(b))(c)
     : use leq-antisym; 7, 14


theorem max-assoc-r
* \max(\max(a)(b))(c) == \max(a)(\max(b)(c))

proof
1. \max(\max(a)(b))(c) : chain
    == \max(c)(\max(a)(b))
     : use max-sym;
    == \max(c)(\max(b)(a))
     : use max-sym; at z in \max(c)(z)
    == \max(\max(c)(b))(a)
     : use max-assoc-l;
    == \max(a)(\max(c)(b))
     : use max-sym;
    == \max(a)(\max(b)(c))
     : use max-sym; at z in \max(a)(z)
~~~
