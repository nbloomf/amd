---
title: And
---

The first boolean operator we'll define is $\and$.

~~~ {.mycelium}
type \and :: Bool -> Bool -> Bool

definition def-and
* \and(p)(q) == \if(\if(\true)(\false)(q))(\false)(p)
~~~

We'll start by computing $\and$ explicitly.

~~~ {.mycelium}
theorem and-true-true
* \and(\true)(\true) == \true

proof
1. \and(\true)(\true) : chain
    == \if(\if(\true)(\false)(\true))(\false)(\true) : use def-and;
    == \if(\true)(\false)(\true) : use if-true;
    == \true : use if-true;


theorem and-true-false
* \and(\true)(\false) == \false

proof
1. \and(\true)(\false) : chain
    == \if(\if(\true)(\false)(\false))(\false)(\true) : use def-and;
    == \if(\true)(\false)(\false) : use if-true;
    == \false : use if-false;


theorem and-false-l
* \and(\false)(q) == \false

proof
1. \and(\false)(q) : chain
    == \if(\if(\true)(\false)(q))(\false)(\false) : use def-and;
    == \false : use if-false;
~~~

That last equation is saying that $\false$ acts like a zero for $\and$; also $\true$ acts like an identity.

~~~ {.mycelium}
theorem and-true-l
* \and(\true)(q) == q

proof
1.   q == \true : hypothesis q-T
2.     \and(\true)(q) : chain
        == \and(\true)(\true) : hypothesis q-T at w in \and(\true)(w)
        == \true : use and-true-true;
        == q : use eq-sym; 1
3. (q == \true) => (\and(\true)(q) == q) : discharge q-T; 2
4.   q == \false : hypothesis q-F
5.     \and(\true)(q) : chain
         == \and(\true)(\false) : hypothesis q-F at w in \and(\true)(w)
         == \false : use and-true-false;
         == q : use eq-sym; 4
6. (q == \false) => (\and(\true)(q) == q) : discharge q-F; 5
7. \and(\true)(q) == q : use bool-induction; 3, 6
~~~

From here, the usual properties of boolean and are straightforward. $\and$ is idempotent:

~~~ {.mycelium}
theorem and-idemp
* \and(q)(q) == q

proof
1.   q == \true : hypothesis T
2.   \and(q)(q) : chain
       == \and(\true)(q) : hypothesis T at z in \and(z)(q)
       == q : use and-true-l;
3. (q == \true) => (\and(q)(q) == q) : discharge T; 2
4.   q == \false : hypothesis F
5.   \and(q)(q) : chain
       == \and(\false)(q) : hypothesis F at z in \and(z)(q)
       == \false : use and-false-l;
       == q : flop hypothesis F
6. (q == \false) => (\and(q)(q) == q) : discharge F; 5
7. \and(q)(q) == q : use bool-induction; 3, 6
~~~

$\and$ is commutative:

~~~ {.mycelium}
theorem and-comm
* \and(p)(q) == \and(q)(p)

proof
1.    q == \true : hypothesis q-T
2.      p == \true : hypothesis p-T
3.      \and(p)(q) : chain
         == \and(\true)(q) : hypothesis p-T at w in \and(w)(q)
         == \and(\true)(\true)
             : hypothesis q-T at w in \and(\true)(w)
         == \and(q)(\true) : use eq-sym; 1 at w in \and(w)(\true)
         == \and(q)(p) : use eq-sym; 2 at w in \and(q)(w)
4.    (p == \true) => (\and(p)(q) == \and(q)(p)) : discharge p-T; 3
5.      p == \false : hypothesis p-F
6.      \and(p)(q) : chain
         == \and(\false)(q) : hypothesis p-F at w in \and(w)(q)
         == \false : use and-false-l;
         == \and(\true)(\false) : flop use and-true-false;
         == \and(q)(\false) : use eq-sym; 1 at w in \and(w)(\false)
         == \and(q)(p) : use eq-sym; 5 at w in \and(q)(w)
7.    (p == \false) => (\and(p)(q) == \and(q)(p)) : discharge p-F; 6
8.    \and(p)(q) == \and(q)(p) : use bool-induction; 4, 7
9.  (q == \true) => (\and(p)(q) == \and(q)(p)) : discharge q-T; 8
10.   q == \false : hypothesis q-F
11.     p == \true : hypothesis p-T
12.     \and(p)(q) : chain
         == \and(\true)(q) : hypothesis p-T at w in \and(w)(q)
         == \and(\true)(\false)
             : hypothesis q-F at w in \and(\true)(w)
         == \false : use and-true-false;
         == \and(\false)(\true) : flop use and-false-l;
         == \and(q)(\true) : use eq-sym; 10 at w in \and(w)(\true)
         == \and(q)(p) : use eq-sym; 11 at w in \and(q)(w)
13.   (p == \true) => (\and(p)(q) == \and(q)(p)) : discharge p-T; 12
14.     p == \false : hypothesis p-F
15.     \and(p)(q) : chain
         == \and(\false)(q) : hypothesis p-F at w in \and(w)(q)
         == \false : use and-false-l;
         == \and(\false)(p) : flop use and-false-l;
         == \and(q)(p) : use eq-sym; 10 at w in \and(w)(p)
16.   (p == \false) => (\and(p)(q) == \and(q)(p)) : discharge p-F; 15
17.   \and(p)(q) == \and(q)(p) : use bool-induction; 13, 16
18. (q == \false) => (\and(p)(q) == \and(q)(p)) : discharge q-F; 17
19. \and(p)(q) == \and(q)(p) : use bool-induction; 9, 18
~~~

And $\and$ is associative.

~~~ {.mycelium}
theorem and-assoc-l
* \and(p)(\and(q)(r)) == \and(\and(p)(q))(r)

proof
1.   p == \true : hypothesis p-T
2.   \and(p)(\and(q)(r)) : chain
      == \and(\true)(\and(q)(r))
          : hypothesis p-T at w in \and(w)(\and(q)(r))
      == \and(q)(r) : use and-true-l;
      == \and(\and(\true)(q))(r)
          : flop use and-true-l; at w in \and(w)(r)
      == \and(\and(p)(q))(r)
          : use eq-sym; 1 at w in \and(\and(w)(q))(r)
3. (p == \true) => (\and(p)(\and(q)(r)) == \and(\and(p)(q))(r))
    : discharge p-T; 2
4.   p == \false : hypothesis p-F
5.   \and(p)(\and(q)(r)) : chain
      == \and(\false)(\and(q)(r))
          : hypothesis p-F at w in \and(w)(\and(q)(r))
      == \false : use and-false-l;
      == \and(\false)(r) : flop use and-false-l;
      == \and(\and(\false)(q))(r)
          : flop use and-false-l; at w in \and(w)(r)
      == \and(\and(p)(q))(r)
          : use eq-sym; 4 at w in \and(\and(w)(q))(r)
6. (p == \false) => (\and(p)(\and(q)(r)) == \and(\and(p)(q))(r))
    : discharge p-F; 5
7. \and(p)(\and(q)(r)) == \and(\and(p)(q))(r)
    : use bool-induction; 3, 6


theorem and-assoc-r
* \and(\and(p)(q))(r) == \and(p)(\and(q)(r))

proof
1. \and(p)(\and(q)(r)) == \and(\and(p)(q))(r) : use and-assoc-l;
2. \and(\and(p)(q))(r) == \and(p)(\and(q)(r)) : use eq-sym; 1
~~~

