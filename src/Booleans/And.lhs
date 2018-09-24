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
1. \and(\true)(\true) == \true : use and-true-true;
2. \and(\true)(\false) == \false : use and-true-false;
3. ∀u. \and(\true)(u) == u
   : invoke bool-induction [P :-> \and(\true)(_) == _]; 1, 2
4. \and(\true)(q) == q : forall-elim u -> q; 3
~~~

From here, the usual properties of boolean and are straightforward. $\and$ is idempotent:

~~~ {.mycelium}
theorem and-idemp
* \and(q)(q) == q

proof
1. \and(\true)(\true) == \true : use and-true-true;
2. \and(\false)(\false) == \false : use and-false-l;
3. ∀u. \and(u)(u) == u
   : invoke bool-induction [P :-> \and(_)(_) == _]; 1, 2
4. \and(q)(q) == q : forall-elim u -> q; 3
~~~

$\and$ is commutative:

~~~ {.mycelium}
theorem and-comm
* \and(p)(q) == \and(q)(p)

proof
1.  \and(\true)(\true) == \and(\true)(\true) : eq-intro
2.  \and(\true)(\false) : chain
     == \false : use and-true-false;
     == \and(\false)(\true) : flop use and-false-l;
3.  ∀u. \and(\true)(u) == \and(u)(\true)
     : invoke bool-induction [P :-> \and(\true)(_) == \and(_)(\true)]; 1, 2
4.  \and(\true)(q) == \and(q)(\true) : forall-elim u -> q; 3
5.  \and(\false)(\true) : chain
     == \false : use and-false-l;
     == \and(\true)(\false) : flop use and-true-false;
6.  \and(\false)(\false) == \and(\false)(\false) : eq-intro
7.  ∀u. \and(\false)(u) == \and(u)(\false)
     : invoke bool-induction [P :-> \and(\false)(_) == \and(_)(\false)]; 5, 6
8.  \and(\false)(q) == \and(q)(\false) : forall-elim u -> q; 7
9.  ∀u. \and(u)(q) == \and(q)(u)
     : invoke bool-induction [P :-> \and(_)(q) == \and(q)(_)]; 4, 8
10. \and(p)(q) == \and(q)(p) : forall-elim u -> p; 9
~~~

~~~ {.mycelium}
theorem and-false-r
* \and(p)(\false) == \false

proof
1. \and(p)(\false) : chain
    == \and(\false)(p) : use and-comm;
    == \false : use and-false-l;
~~~

And $\and$ is associative.

~~~ {.mycelium}
theorem and-assoc-l
* \and(p)(\and(q)(r)) == \and(\and(p)(q))(r)

proof
1.  \and(\true)(\and(q)(r)) : chain
     == \and(q)(r) : use and-true-l;
     == \and(\and(\true)(q))(r) : flop use and-true-l; at z in \and(z)(r)
2.  \and(\false)(\and(q)(r)) : chain
     == \false : use and-false-l;
     == \and(\false)(r) : flop use and-false-l;
     == \and(\and(\false)(q))(r) : flop use and-false-l; at z in \and(z)(r)
3.  ∀u. \and(u)(\and(q)(r)) == \and(\and(u)(q))(r)
     : invoke bool-induction [P :-> \and(_)(\and(q)(r)) == \and(\and(_)(q))(r)]; 1, 2
4. \and(p)(\and(q)(r)) == \and(\and(p)(q))(r) : forall-elim u -> p; 3


theorem and-assoc-r
* \and(\and(p)(q))(r) == \and(p)(\and(q)(r))

proof
1. \and(p)(\and(q)(r)) == \and(\and(p)(q))(r) : use and-assoc-l;
2. \and(\and(p)(q))(r) == \and(p)(\and(q)(r)) : use eq-sym; 1
~~~

~~~ {.mycelium}
theorem and-conj
if
  * \and(p)(q) == \true
then
  * (p == \true) /\ (q == \true)

proof
1.  (p == \true) \/ (p == \false) : use bool-cases;
2.    p == \false : hypothesis p-false
3.    \true : chain
       == \and(p)(q) : flop assumption 1
       == \and(\false)(q) : hypothesis p-false at z in \and(z)(q)
       == \false : use and-false-l;
4.  (p == \false) => (\true == \false) : discharge p-false; 3
5.  ~(\true == \false) : use bool-disc;
6.  ~(p == \false) : use modus-tollens; 4, 5
7.  p == \true : use disj-syllogism-r; 1, 6
8.  (q == \true) \/ (q == \false) : use bool-cases;
9.    q == \false : hypothesis q-false
10.   \true : chain
       == \and(p)(q) : flop assumption 1
       == \and(p)(\false) : hypothesis q-false at z in \and(p)(z)
       == \false : use and-false-r;
11. (q == \false) => (\true == \false) : discharge q-false; 10
12. ~(\true == \false) : use bool-disc;
13. ~(q == \false) : use modus-tollens; 11, 12
14. q == \true : use disj-syllogism-r; 8, 13
15. (p == \true) /\ (q == \true) : use conj-intro; 7, 14
~~~
