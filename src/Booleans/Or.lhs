---
title: Or
---

Next we define $\or$.

~~~ {.mycelium}
type \or :: Bool -> Bool -> Bool

rule def-or
* \or(p)(q) == \if(\true)(\if(\true)(\false)(q))(p)
~~~

And we can compute $\or$ explicitly.

~~~ {.mycelium}
theorem or-false-false
* \or(\false)(\false) == \false

proof
1. \or(\false)(\false) : chain
    == \if(\true)(\if(\true)(\false)(\false))(\false) : use def-or;
    == \if(\true)(\false)(\false) : use if-false;
    == \false : use if-false;

theorem or-false-true
* \or(\false)(\true) == \true

proof
1. \or(\false)(\true) : chain
    == \if(\true)(\if(\true)(\false)(\true))(\false) : use def-or;
    == \if(\true)(\false)(\true) : use if-false;
    == \true : use if-true;

theorem or-true-l
* \or(\true)(q) == \true

proof
1. \or(\true)(q) : chain
    == \if(\true)(\if(\true)(\false)(q))(\true) : use def-or;
    == \true : use if-true;
~~~

That last property says that $\true$ acts like a zero for $\or$; we can also say $\false$ acts like an identity.

~~~ {.mycelium}
theorem or-false-l
* \or(\false)(q) == q

proof
1.   q == \true : hypothesis q-T
2.   \or(\false)(q) : chain
      == \or(\false)(\true) : hypothesis q-T at w in \or(\false)(w)
      == \true : use or-false-true;
      == q : use eq-sym; 1
3. (q == \true) => (\or(\false)(q) == q) : discharge q-T; 2
4.   q == \false : hypothesis q-F
5.   \or(\false)(q) : chain
      == \or(\false)(\false) : hypothesis q-F at w in \or(\false)(w)
      == \false : use or-false-false;
      == q : use eq-sym; 4
6. (q == \false) => (\or(\false)(q) == q) : discharge q-F; 5
7. \or(\false)(q) == q : use bool-induction; 3, 6
~~~

From here the other properties of $\or$ are straightforward. It is idempotent:

~~~ {.mycelium}
theorem or-idemp
* \or(q)(q) == q

proof
1.   q == \true : hypothesis T
2.   \or(q)(q) : chain
      == \or(\true)(q) : hypothesis T at z in \or(z)(q)
      == \true : use or-true-l;
      == q : flop hypothesis T
3. (q == \true) => (\or(q)(q) == q) : discharge T; 2
4.   q == \false : hypothesis F
5.   \or(q)(q) : chain
      == \or(\false)(q) : hypothesis F at z in \or(z)(q)
      == q : use or-false-l;
6. (q == \false) => (\or(q)(q) == q) : discharge F; 5
7. \or(q)(q) == q : use bool-induction; 3, 6
~~~

$\or$ is commutative:

~~~ {.mycelium}
theorem or-comm
* \or(p)(q) == \or(q)(p)

proof
1.    q == \true : hypothesis q-T
2.      p == \true : hypothesis p-T
3.      \or(p)(q) : chain
         == \or(\true)(q) : hypothesis p-T at z in \or(z)(q)
         == \true : use or-true-l;
         == \or(\true)(p) : flop use or-true-l;
         == \or(q)(p) : flop hypothesis q-T at z in \or(z)(p)
4.    (p == \true) => (\or(p)(q) == \or(q)(p)) : discharge p-T; 3
5.      p == \false : hypothesis p-F
6.      \or(p)(q) : chain
         == \or(\false)(q) : hypothesis p-F at z in \or(z)(q)
         == q : use or-false-l;
         == \true : hypothesis q-T
         == \or(\true)(p) : flop use or-true-l;
         == \or(q)(p) : flop hypothesis q-T at z in \or(z)(p)
7.    (p == \false) => (\or(p)(q) == \or(q)(p)) : discharge p-F; 6
8.    \or(p)(q) == \or(q)(p) : use bool-induction; 4, 7
9.  (q == \true) => (\or(p)(q) == \or(q)(p)) : discharge q-T; 8
10.   q == \false : hypothesis q-F
11.     p == \true : hypothesis p-T
12.     \or(p)(q) : chain
         == \or(\true)(q) : hypothesis p-T at z in \or(z)(q)
         == \true : use or-true-l;
         == \or(\false)(\true) : flop use or-false-true;
         == \or(q)(\true) : flop hypothesis q-F at z in \or(z)(\true)
         == \or(q)(p) : flop hypothesis p-T at z in \or(q)(z)
13.   (p == \true) => (\or(p)(q) == \or(q)(p)) : discharge p-T; 12
14.     p == \false : hypothesis p-F
15.     \or(p)(q) : chain
         == \or(\false)(q) : hypothesis p-F at z in \or(z)(q)
         == q : use or-false-l;
         == \false : hypothesis q-F
         == p : flop hypothesis p-F
         == \or(\false)(p) : flop use or-false-l;
         == \or(q)(p) : flop hypothesis q-F at z in \or(z)(p)
16.   (p == \false) => (\or(p)(q) == \or(q)(p)) : discharge p-F; 15
17.   \or(p)(q) == \or(q)(p) : use bool-induction; 13, 16
18. (q == \false) => (\or(p)(q) == \or(q)(p)) : discharge q-F; 17
19. \or(p)(q) == \or(q)(p) : use bool-induction; 9, 18
~~~

And $\or$ is associative.

~~~ {.mycelium}
theorem or-assoc-l
* \or(p)(\or(q)(r)) == \or(\or(p)(q))(r)

proof
1.   p == \true : hypothesis p-T
2.   \or(p)(\or(q)(r)) : chain
      == \or(\true)(\or(q)(r))
          : hypothesis p-T at z in \or(z)(\or(q)(r))
      == \true : use or-true-l;
      == \or(\true)(r) : flop use or-true-l;
      == \or(\or(\true)(q))(r)
          : flop use or-true-l; at z in \or(z)(r)
      == \or(\or(p)(q))(r)
          : flop hypothesis p-T at z in \or(\or(z)(q))(r)
3. (p == \true) => (\or(p)(\or(q)(r)) == \or(\or(p)(q))(r))
    : discharge p-T; 2
4.   p == \false : hypothesis p-F
5.   \or(p)(\or(q)(r)) : chain
      == \or(\false)(\or(q)(r))
          : hypothesis p-F at z in \or(z)(\or(q)(r))
      == \or(q)(r) : use or-false-l;
      == \or(\or(\false)(q))(r)
          : flop use or-false-l; at z in \or(z)(r)
      == \or(\or(p)(q))(r)
          : flop hypothesis p-F at z in \or(\or(z)(q))(r)
6. (p == \false) => (\or(p)(\or(q)(r)) == \or(\or(p)(q))(r))
    : discharge p-F; 5
7. \or(p)(\or(q)(r)) == \or(\or(p)(q))(r)
    : use bool-induction; 3, 6


theorem or-assoc-r
* \or(\or(p)(q))(r) == \or(p)(\or(q)(r))

proof
1. \or(p)(\or(q)(r)) == \or(\or(p)(q))(r) : use or-assoc-l;
2. \or(\or(p)(q))(r) == \or(p)(\or(q)(r)) : use eq-sym; 1
~~~

$\or$ also distributes over $\and$.

~~~ {.mycelium}
theorem or-and-dist-l
* \or(p)(\and(q)(r)) == \and(\or(p)(q))(\or(p)(r))

proof
1.   p == \true : hypothesis p-T
2.   \or(p)(\and(q)(r)) : chain
      == \or(\true)(\and(q)(r))
          : hypothesis p-T at z in \or(z)(\and(q)(r))
      == \true : use or-true-l;
      == \and(\true)(\true) : flop use and-true-true;
      == \and(\or(\true)(q))(\true)
          : flop use or-true-l; at z in \and(z)(\true)
      == \and(\or(\true)(q))(\or(\true)(r))
          : flop use or-true-l; at z in \and(\or(\true)(q))(z)
      == \and(\or(p)(q))(\or(p)(r))
          : flop hypothesis p-T at z in \and(\or(z)(q))(\or(z)(r))
3. (p == \true) => (\or(p)(\and(q)(r)) == \and(\or(p)(q))(\or(p)(r)))
    : discharge p-T; 2
4.   p == \false : hypothesis p-F
5.   \or(p)(\and(q)(r)) : chain
      == \or(\false)(\and(q)(r))
          : hypothesis p-F at z in \or(z)(\and(q)(r))
      == \and(q)(r) : use or-false-l;
      == \and(\or(\false)(q))(r)
          : flop use or-false-l; at z in \and(z)(r)
      == \and(\or(\false)(q))(\or(\false)(r))
          : flop use or-false-l; at z in \and(\or(\false)(q))(z)
      == \and(\or(p)(q))(\or(p)(r))
          : flop hypothesis p-F at z in \and(\or(z)(q))(\or(z)(r))
6. (p == \false) => (\or(p)(\and(q)(r)) == \and(\or(p)(q))(\or(p)(r)))
    : discharge p-F; 5
7. \or(p)(\and(q)(r)) == \and(\or(p)(q))(\or(p)(r))
    : use bool-induction; 3, 6


theorem or-and-dist-r
* \or(\and(p)(q))(r) == \and(\or(p)(r))(\or(q)(r))

proof
1. \or(\and(p)(q))(r) : chain
    == \or(r)(\and(p)(q)) : use or-comm;
    == \and(\or(r)(p))(\or(r)(q))
        : use or-and-dist-l;
    == \and(\or(p)(r))(\or(r)(q))
        : use or-comm; at z in \and(z)(\or(r)(q))
    == \and(\or(p)(r))(\or(q)(r))
        : use or-comm; at z in \and(\or(p)(r))(z)
~~~

And $\and$ distributes over $\or$.

~~~ {.mycelium}
theorem and-or-dist-l
* \and(p)(\or(q)(r)) == \or(\and(p)(q))(\and(p)(r))

proof
1.   p == \true : hypothesis p-T
2.   \and(p)(\or(q)(r)) : chain
      == \and(\true)(\or(q)(r))
          : hypothesis p-T at z in \and(z)(\or(q)(r))
      == \or(q)(r) : use and-true-l;
      == \or(\and(\true)(q))(r)
          : flop use and-true-l; at z in \or(z)(r)
      == \or(\and(\true)(q))(\and(\true)(r))
          : flop use and-true-l; at z in \or(\and(\true)(q))(z)
      == \or(\and(p)(q))(\and(p)(r))
          : flop hypothesis p-T at z in \or(\and(z)(q))(\and(z)(r))
3. (p == \true) => (\and(p)(\or(q)(r)) == \or(\and(p)(q))(\and(p)(r)))
    : discharge p-T; 2
4.   p == \false : hypothesis p-F
5.   \and(p)(\or(q)(r)) : chain
      == \and(\false)(\or(q)(r))
          : hypothesis p-F at z in \and(z)(\or(q)(r))
      == \false : use and-false-l;
      == \or(\false)(\false) : flop use or-false-false;
      == \or(\and(\false)(q))(\false)
          : flop use and-false-l; at z in \or(z)(\false)
      == \or(\and(\false)(q))(\and(\false)(r))
          : flop use and-false-l; at z in \or(\and(\false)(q))(z)
      == \or(\and(p)(q))(\and(p)(r))
          : flop hypothesis p-F at z in \or(\and(z)(q))(\and(z)(r))
6. (p == \false) => (\and(p)(\or(q)(r)) == \or(\and(p)(q))(\and(p)(r)))
    : discharge p-F; 5
7. \and(p)(\or(q)(r)) == \or(\and(p)(q))(\and(p)(r))
    : use bool-induction; 3, 6


theorem and-or-dist-r
* \and(\or(p)(q))(r) == \or(\and(p)(r))(\and(q)(r))

proof
1. \and(\or(p)(q))(r) : chain
    == \and(r)(\or(p)(q)) : use and-comm;
    == \or(\and(r)(p))(\and(r)(q))
        : use and-or-dist-l;
    == \or(\and(p)(r))(\and(r)(q))
        : use and-comm; at z in \or(z)(\and(r)(q))
    == \or(\and(p)(r))(\and(q)(r))
        : use and-comm; at z in \or(\and(p)(r))(z)
~~~
