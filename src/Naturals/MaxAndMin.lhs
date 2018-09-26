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
theorem max-comm
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
    == \max(b)(a) : use max-comm;
    == a : use leq-impl-max; 2
~~~

~~~ {.mycelium}
theorem min-comm
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
    == \min(b)(a) : use min-comm;
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
     : use max-comm; at z in
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
     : use min-comm; at z in
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
      : use max-comm; at z in
        \leq(b)(z)
     == \true
      : use leq-leq-max; 9
11. \leq(\max(a)(b))(\max(a)(\max(b)(c))) == \true
     : use max-glb; 8, 10
12. \leq(c)(\max(b)(c)) == \true
     : use leq-max-r;
13. \leq(c)(\max(a)(\max(b)(c))) : chain
     == \leq(c)(\max(\max(b)(c))(a))
      : use max-comm; at z in
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
     : use max-comm;
    == \max(c)(\max(b)(a))
     : use max-comm; at z in \max(c)(z)
    == \max(\max(c)(b))(a)
     : use max-assoc-l;
    == \max(a)(\max(c)(b))
     : use max-comm;
    == \max(a)(\max(b)(c))
     : use max-comm; at z in \max(a)(z)
~~~

~~~ {.mycelium}
theorem min-assoc-l
* \min(a)(\min(b)(c)) == \min(\min(a)(b))(c)

proof
1.  \leq(\min(a)(b))(a) == \true
     : use leq-min-l;
2.  \leq(\min(\min(a)(b))(c))(a) == \true
     : use leq-leq-min; 1
3.  \leq(\min(a)(b))(b) == \true
     : use leq-min-r;
4.  \leq(\min(\min(a)(b))(c))(b) == \true
     : use leq-leq-min; 3
5.  \leq(\min(\min(a)(b))(c))(c) == \true
     : use leq-min-r;
6.  \leq(\min(\min(a)(b))(c))(\min(b)(c)) == \true
     : use min-lub; 4, 5
7.  \leq(\min(\min(a)(b))(c))(\min(a)(\min(b)(c))) == \true
     : use min-lub; 2, 6
8.  \leq(\min(a)(\min(b)(c)))(a) == \true
     : use leq-min-l;
9.  \leq(\min(b)(c))(b) == \true
     : use leq-min-l;
10. \leq(\min(a)(\min(b)(c)))(b) : chain
     == \leq(\min(\min(b)(c))(a))(b)
      : use min-comm; at z in
        \leq(z)(b)
     == \true
      : use leq-leq-min; 9
11. \leq(\min(a)(\min(b)(c)))(\min(a)(b)) == \true
     : use min-lub; 8, 10
12. \leq(\min(b)(c))(c) == \true
     : use leq-min-r;
13. \leq(\min(a)(\min(b)(c)))(c) : chain
     == \leq(\min(\min(b)(c))(a))(c)
      : use min-comm; at z in
        \leq(z)(c)
     == \true
      : use leq-leq-min; 12
14. \leq(\min(a)(\min(b)(c)))(\min(\min(a)(b))(c)) == \true
     : use min-lub; 11, 13
15. \min(a)(\min(b)(c)) == \min(\min(a)(b))(c)
     : use leq-antisym; 14, 7


theorem min-assoc-r
* \min(\min(a)(b))(c) == \min(a)(\min(b)(c))

proof
1. \min(\min(a)(b))(c) : chain
    == \min(c)(\min(a)(b))
     : use min-comm;
    == \min(c)(\min(b)(a))
     : use min-comm; at z in \min(c)(z)
    == \min(\min(c)(b))(a)
     : use min-assoc-l;
    == \min(a)(\min(c)(b))
     : use min-comm;
    == \min(a)(\min(b)(c))
     : use min-comm; at z in \min(a)(z)
~~~

~~~ {.mycelium}
theorem plus-max-dist-l
* \plus(a)(\max(b)(c)) == \max(\plus(a)(b))(\plus(a)(c))

proof
1. \plus(\zero)(\max(b)(c)) : chain
    == \max(b)(c)
     : use plus-zero-l;
    == \max(\plus(\zero)(b))(c)
     : flop use plus-zero-l; at z in
       \max(z)(c)
    == \max(\plus(\zero)(b))(\plus(\zero)(c))
     : flop use plus-zero-l; at z in
       \max(\plus(\zero)(b))(z)

2.   \plus(n)(\max(b)(c))
      == \max(\plus(n)(b))(\plus(n)(c))
      : hypothesis n

3.   \plus(\next(n))(\max(b)(c)) : chain
      == \next(\plus(n)(\max(b)(c)))
       : use plus-next-l;
      == \next(\max(\plus(n)(b))(\plus(n)(c)))
       : hypothesis n at z in \next(z)
      == \max(\next(\plus(n)(b)))(\next(\plus(n)(c)))
       : flop use max-next-next;
      == \max(\plus(\next(n))(b))(\next(\plus(n)(c)))
       : flop use plus-next-l; at z in
         \max(z)(\next(\plus(n)(c)))
      == \max(\plus(\next(n))(b))(\plus(\next(n))(c))
       : flop use plus-next-l; at z in
         \max(\plus(\next(n))(b))(z)

4. (\plus(n)(\max(b)(c))
       == \max(\plus(n)(b))(\plus(n)(c))) =>
     (\plus(\next(n))(\max(b)(c))
         == \max(\plus(\next(n))(b))(\plus(\next(n))(c)))
    : discharge n; 3

5. ∀k. (\plus(k)(\max(b)(c))
       == \max(\plus(k)(b))(\plus(k)(c))) =>
     (\plus(\next(k))(\max(b)(c))
         == \max(\plus(\next(k))(b))(\plus(\next(k))(c)))
    : forall-intro n -> k; 4

6. ∀k. \plus(k)(\max(b)(c))
    == \max(\plus(k)(b))(\plus(k)(c))
    : invoke nat-induction
      [P :-> \plus(_)(\max(b)(c))
               == \max(\plus(_)(b))(\plus(_)(c))]; 1, 5

7. \plus(a)(\max(b)(c))
    == \max(\plus(a)(b))(\plus(a)(c))
     : forall-elim k -> a; 6


theorem plus-max-dist-r
* \plus(\max(a)(b))(c) == \max(\plus(a)(c))(\plus(b)(c))

proof
1. \plus(\max(a)(b))(c) : chain
    == \plus(c)(\max(a)(b))
     : use plus-comm;
    == \max(\plus(c)(a))(\plus(c)(b))
     : use plus-max-dist-l;
    == \max(\plus(a)(c))(\plus(c)(b))
     : use plus-comm; at z in
       \max(z)(\plus(c)(b))
    == \max(\plus(a)(c))(\plus(b)(c))
     : use plus-comm; at z in
       \max(\plus(a)(c))(z)
~~~

~~~ {.mycelium}
theorem plus-min-dist-l
* \plus(a)(\min(b)(c)) == \min(\plus(a)(b))(\plus(a)(c))

proof
1. \plus(\zero)(\min(b)(c)) : chain
    == \min(b)(c)
     : use plus-zero-l;
    == \min(\plus(\zero)(b))(c)
     : flop use plus-zero-l; at z in
       \min(z)(c)
    == \min(\plus(\zero)(b))(\plus(\zero)(c))
     : flop use plus-zero-l; at z in
       \min(\plus(\zero)(b))(z)

2.   \plus(n)(\min(b)(c))
      == \min(\plus(n)(b))(\plus(n)(c))
      : hypothesis n

3.   \plus(\next(n))(\min(b)(c)) : chain
      == \next(\plus(n)(\min(b)(c)))
       : use plus-next-l;
      == \next(\min(\plus(n)(b))(\plus(n)(c)))
       : hypothesis n at z in \next(z)
      == \min(\next(\plus(n)(b)))(\next(\plus(n)(c)))
       : flop use min-next-next;
      == \min(\plus(\next(n))(b))(\next(\plus(n)(c)))
       : flop use plus-next-l; at z in
         \min(z)(\next(\plus(n)(c)))
      == \min(\plus(\next(n))(b))(\plus(\next(n))(c))
       : flop use plus-next-l; at z in
         \min(\plus(\next(n))(b))(z)

4. (\plus(n)(\min(b)(c))
       == \min(\plus(n)(b))(\plus(n)(c))) =>
     (\plus(\next(n))(\min(b)(c))
         == \min(\plus(\next(n))(b))(\plus(\next(n))(c)))
    : discharge n; 3

5. ∀k. (\plus(k)(\min(b)(c))
       == \min(\plus(k)(b))(\plus(k)(c))) =>
     (\plus(\next(k))(\min(b)(c))
         == \min(\plus(\next(k))(b))(\plus(\next(k))(c)))
    : forall-intro n -> k; 4

6. ∀k. \plus(k)(\min(b)(c))
    == \min(\plus(k)(b))(\plus(k)(c))
    : invoke nat-induction
      [P :-> \plus(_)(\min(b)(c))
               == \min(\plus(_)(b))(\plus(_)(c))]; 1, 5

7. \plus(a)(\min(b)(c))
    == \min(\plus(a)(b))(\plus(a)(c))
     : forall-elim k -> a; 6


theorem plus-min-dist-r
* \plus(\min(a)(b))(c) == \min(\plus(a)(c))(\plus(b)(c))

proof
1. \plus(\min(a)(b))(c) : chain
    == \plus(c)(\min(a)(b))
     : use plus-comm;
    == \min(\plus(c)(a))(\plus(c)(b))
     : use plus-min-dist-l;
    == \min(\plus(a)(c))(\plus(c)(b))
     : use plus-comm; at z in
       \min(z)(\plus(c)(b))
    == \min(\plus(a)(c))(\plus(b)(c))
     : use plus-comm; at z in
       \min(\plus(a)(c))(z)
~~~

~~~ {.mycelium}
theorem leq-min-max
* \leq(\min(a)(b))(\max(a)(b)) == \true

proof
1. \leq(\min(a)(b))(a) == \true
    : use leq-min-l;
2. \leq(\min(a)(b))(\max(a)(b)) == \true
    : use leq-leq-max; 1
~~~

~~~ {.mycelium}
theorem min-max-dist-l
* \min(a)(\max(b)(c)) == \max(\min(a)(b))(\min(a)(c))

proof
1.  \leq(b)(\max(b)(c)) == \true
     : use leq-max-l;
2.  \leq(\min(a)(b))(b) == \true
     : use leq-min-r;
3.  \leq(\min(a)(b))(\max(b)(c)) == \true
     : use leq-trans; 2, 1
4.  \leq(\min(a)(b))(a) == \true
     : use leq-min-l;
5.  \leq(\min(a)(b))(\min(a)(\max(b)(c))) == \true
     : use min-lub; 4, 3
6.  \leq(c)(\max(b)(c)) == \true
     : use leq-max-r;
7.  \leq(\min(a)(c))(c) == \true
     : use leq-min-r;
8.  \leq(\min(a)(c))(\max(b)(c)) == \true
     : use leq-trans; 7, 6
9.  \leq(\min(a)(c))(a) == \true
     : use leq-min-l;
10. \leq(\min(a)(c))(\min(a)(\max(b)(c))) == \true
     : use min-lub; 9, 8
11. \leq(
      \max(\min(a)(b))(\min(a)(c)))(
      \min(a)(\max(b)(c)))
       == \true
     : use max-glb; 5, 10
12. (\max(b)(c) == b) \/ (\max(b)(c) == c)
     : use max-cases;
13.   \max(b)(c) == b : hypothesis b
14.   \leq(\min(a)(\max(b)(c)))(\min(a)(b)) : chain
       == \leq(\min(a)(b))(\min(a)(b))
        : hypothesis b at z in
          \leq(\min(a)(z))(\min(a)(b))
       == \true
        : use leq-refl;
15.   \leq(\min(a)(b))(\max(\min(a)(b))(\min(a)(c))) == \true
       : use leq-max-l;
16.   \leq(
        \min(a)(\max(b)(c)))(
        \max(\min(a)(b))(\min(a)(c)))
         == \true
       : use leq-trans; 14, 15
17. (\max(b)(c) == b) =>
      (\leq(
        \min(a)(\max(b)(c)))(
        \max(\min(a)(b))(\min(a)(c)))
         == \true)
     : discharge b; 16
18.   \max(b)(c) == c : hypothesis c
19.   \leq(\min(a)(\max(b)(c)))(\min(a)(c)) : chain
       == \leq(\min(a)(c))(\min(a)(c))
        : hypothesis c at z in
          \leq(\min(a)(z))(\min(a)(c))
       == \true
        : use leq-refl;
20.   \leq(\min(a)(c))(\max(\min(a)(b))(\min(a)(c))) == \true
       : use leq-max-r;
21.   \leq(
        \min(a)(\max(b)(c)))(
        \max(\min(a)(b))(\min(a)(c)))
         == \true
       : use leq-trans; 19, 20
22. (\max(b)(c) == c) =>
      (\leq(
        \min(a)(\max(b)(c)))(
        \max(\min(a)(b))(\min(a)(c)))
         == \true)
     : discharge c; 21
23. \leq(
      \min(a)(\max(b)(c)))(
      \max(\min(a)(b))(\min(a)(c)))
       == \true
      : use disj-elim; 12, 17, 22
24. \min(a)(\max(b)(c)) == \max(\min(a)(b))(\min(a)(c))
     : use leq-antisym; 23, 11


theorem min-max-dist-r
* \min(\max(a)(b))(c) == \max(\min(a)(c))(\min(b)(c))

proof
1. \min(\max(a)(b))(c) : chain
    == \min(c)(\max(a)(b))
     : use min-comm;
    == \max(\min(c)(a))(\min(c)(b))
     : use min-max-dist-l;
    == \max(\min(a)(c))(\min(c)(b))
     : use min-comm; at z in
       \max(z)(\min(c)(b))
    == \max(\min(a)(c))(\min(b)(c))
     : use min-comm; at z in
       \max(\min(a)(c))(z)
~~~

~~~ {.mycelium}
theorem max-min-dist-l
* \max(a)(\min(b)(c)) == \min(\max(a)(b))(\max(a)(c))

proof
1.  \leq(\min(b)(c))(b) == \true
     : use leq-min-l;
2.  \leq(b)(\max(a)(b)) == \true
     : use leq-max-r;
3.  \leq(\min(b)(c))(\max(a)(b)) == \true
     : use leq-trans; 1, 2
4.  \leq(a)(\max(a)(b)) == \true
     : use leq-max-l;
5.  \leq(\max(a)(\min(b)(c)))(\max(a)(b)) == \true
     : use max-glb; 4, 3
6.  \leq(\min(b)(c))(c) == \true
     : use leq-min-r;
7.  \leq(c)(\max(a)(c)) == \true
     : use leq-max-r;
8.  \leq(\min(b)(c))(\max(a)(c)) == \true
     : use leq-trans; 6, 7
9.  \leq(a)(\max(a)(c)) == \true
     : use leq-max-l;
10. \leq(\max(a)(\min(b)(c)))(\max(a)(c)) == \true
     : use max-glb; 9, 8
11. \leq(
      \max(a)(\min(b)(c)))(
      \min(\max(a)(b))(\max(a)(c)))
       == \true
     : use min-lub; 5, 10
12. (\min(b)(c) == b) \/ (\min(b)(c) == c)
     : use min-cases;
13.   \min(b)(c) == b : hypothesis b
14.   \leq(\max(a)(b))(\max(a)(\min(b)(c))) : chain
       == \leq(\max(a)(b))(\max(a)(b))
        : hypothesis b at z in
          \leq(\max(a)(b))(\max(a)(z))
       == \true
        : use leq-refl;
15.   \leq(\min(\max(a)(b))(\max(a)(c)))(\max(a)(b)) == \true
       : use leq-min-l;
16.   \leq(
        \min(\max(a)(b))(\max(a)(c)))(
        \max(a)(\min(b)(c)))
         == \true
       : use leq-trans; 15, 14
17. (\min(b)(c) == b) =>
      (\leq(
        \min(\max(a)(b))(\max(a)(c)))(
        \max(a)(\min(b)(c)))
         == \true)
     : discharge b; 16
18.   \min(b)(c) == c : hypothesis c
19.   \leq(\max(a)(c))(\max(a)(\min(b)(c))) : chain
       == \leq(\max(a)(c))(\max(a)(c))
        : hypothesis c at z in
          \leq(\max(a)(c))(\max(a)(z))
       == \true
        : use leq-refl;
20.   \leq(\min(\max(a)(b))(\max(a)(c)))(\max(a)(c)) == \true
       : use leq-min-r;
21.   \leq(
        \min(\max(a)(b))(\max(a)(c)))(
        \max(a)(\min(b)(c)))
         == \true
       : use leq-trans; 20, 19
22. (\min(b)(c) == c) =>
      (\leq(
        \min(\max(a)(b))(\max(a)(c)))(
        \max(a)(\min(b)(c)))
         == \true)
     : discharge c; 21
23. \leq(
      \min(\max(a)(b))(\max(a)(c)))(
      \max(a)(\min(b)(c)))
       == \true
      : use disj-elim; 12, 17, 22
24. \max(a)(\min(b)(c)) == \min(\max(a)(b))(\max(a)(c))
     : use leq-antisym; 11, 23


theorem max-min-dist-r
* \max(\min(a)(b))(c) == \min(\max(a)(c))(\max(b)(c))

proof
1. \max(\min(a)(b))(c) : chain
    == \max(c)(\min(a)(b))
     : use max-comm;
    == \min(\max(c)(a))(\max(c)(b))
     : use max-min-dist-l;
    == \min(\max(a)(c))(\max(c)(b))
     : use max-comm; at z in
       \min(z)(\max(c)(b))
    == \min(\max(a)(c))(\max(b)(c))
     : use max-comm; at z in
       \min(\max(a)(c))(z)
~~~
