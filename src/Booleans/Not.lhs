---
title: Not
---

Next we define boolean $\not$.

~~~ {.mycelium}
type \not :: Bool -> Bool

rule def-not
* \not(q) == \if(\false)(\true)(q)
~~~

We can explicitly compute $\not$:

~~~ {.mycelium}
theorem not-true
* \not(\true) == \false

proof
1. \not(\true) : chain
    == \if(\false)(\true)(\true) : use def-not;
    == \false : use if-true;


theorem not-false
* \not(\false) == \true

proof
1. \not(\false) : chain
    == \if(\false)(\true)(\false) : use def-not;
    == \true : use if-false;
~~~

Now $\not$ is an involution.

~~~ {.mycelium}
theorem not-invol
* \comp(\not)(\not) == \id

proof
1.   p == \true : hypothesis p-T
2.   \comp(\not)(\not)(p) : chain
      == \comp(\not)(\not)(\true)
          : hypothesis p-T at z in \comp(\not)(\not)(z)
      == \not(\not(\true)) : use def-comp;
      == \not(\false) : use not-true; at z in \not(z)
      == \true : use not-false;
      == p : flop hypothesis p-T
      == \id(p) : flop use def-id;
3. (p == \true) => (\comp(\not)(\not)(p) == \id(p))
    : discharge p-T; 2
4.   p == \false : hypothesis p-F
5.   \comp(\not)(\not)(p) : chain
      == \comp(\not)(\not)(\false)
          : hypothesis p-F at z in \comp(\not)(\not)(z)
      == \not(\not(\false)) : use def-comp;
      == \not(\true) : use not-false; at z in \not(z)
      == \false : use not-true;
      == p : flop hypothesis p-F
      == \id(p) : flop use def-id;
6. (p == \false) => (\comp(\not)(\not)(p) == \id(p))
    : discharge p-F; 5
7. \comp(\not)(\not)(p) == \id(p) : use bool-induction; 3, 6
8. ∀x. \comp(\not)(\not)(x) == \id(x) : forall-intro p -> x; 7
9. \comp(\not)(\not) == \id : use fun-eq; 8
~~~

And we have DeMorgan's laws: $\not$ distributes over $\or$ (kind of):

~~~ {.mycelium}
theorem not-or
* \not(\or(p)(q)) == \and(\not(p))(\not(q))

proof
1.   p == \true : hypothesis p-T
2.   \not(\or(p)(q)) : chain
      == \not(\or(\true)(q))
          : hypothesis p-T at z in \not(\or(z)(q))
      == \not(\true)
          : use or-true-l; at z in \not(z)
      == \false : use not-true;
      == \and(\false)(\not(q)) : flop use and-false-l;
      == \and(\not(\true))(\not(q))
          : flop use not-true; at z in \and(z)(\not(q))
      == \and(\not(p))(\not(q))
          : flop hypothesis p-T at z in \and(\not(z))(\not(q))
3. (p == \true) => (\not(\or(p)(q)) == \and(\not(p))(\not(q)))
    : discharge p-T; 2
4.   p == \false : hypothesis p-F
5.   \not(\or(p)(q)) : chain
      == \not(\or(\false)(q))
          : hypothesis p-F at z in \not(\or(z)(q))
      == \not(q)
          : use or-false-l; at z in \not(z)
      == \and(\true)(\not(q)) : flop use and-true-l;
      == \and(\not(\false))(\not(q))
          : flop use not-false; at z in \and(z)(\not(q))
      == \and(\not(p))(\not(q))
          : flop hypothesis p-F at z in \and(\not(z))(\not(q))
6. (p == \false) => (\not(\or(p)(q)) == \and(\not(p))(\not(q)))
    : discharge p-F; 5
7. \not(\or(p)(q)) == \and(\not(p))(\not(q))
    : use bool-induction; 3, 6
~~~

And $\not$ distributes over $\and$ (kind of).

~~~ {.mycelium}
theorem not-and
* \not(\and(p)(q)) == \or(\not(p))(\not(q))

proof
1.   p == \true : hypothesis p-T
2.   \not(\and(p)(q)) : chain
      == \not(\and(\true)(q))
          : hypothesis p-T at z in \not(\and(z)(q))
      == \not(q) : use and-true-l; at z in \not(z)
      == \or(\false)(\not(q)) : flop use or-false-l;
      == \or(\not(\true))(\not(q))
          : flop use not-true; at z in \or(z)(\not(q))
      == \or(\not(p))(\not(q))
          : flop hypothesis p-T at z in \or(\not(z))(\not(q))
3. (p == \true) => (\not(\and(p)(q)) == \or(\not(p))(\not(q)))
    : discharge p-T; 2
4.   p == \false : hypothesis p-F
5.   \not(\and(p)(q)) : chain
      == \not(\and(\false)(q))
          : hypothesis p-F at z in \not(\and(z)(q))
      == \not(\false) : use and-false-l; at z in \not(z)
      == \true : use not-false;
      == \or(\true)(\not(q))
          : flop use or-true-l;
      == \or(\not(\false))(\not(q))
          : flop use not-false; at z in \or(z)(\not(q))
      == \or(\not(p))(\not(q))
          : flop hypothesis p-F at z in \or(\not(z))(\not(q))
6. (p == \false) => (\not(\and(p)(q)) == \or(\not(p))(\not(q)))
    : discharge p-F; 5
7. \not(\and(p)(q)) == \or(\not(p))(\not(q))
    : use bool-induction; 3, 6
~~~
