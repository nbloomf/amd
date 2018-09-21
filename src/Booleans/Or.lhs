---
title: Or
---

Next we define $\or$.

~~~ {.mycelium}
type \or :: Bool -> Bool -> Bool

definition def-or
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
1. \or(\false)(\true) == \true : use or-false-true;
2. \or(\false)(\false) == \false : use or-false-false;
3. ∀u. \or(\false)(u) == u
    : invoke bool-induction [P :-> \or(\false)(_) == _]; 1, 2
4. \or(\false)(q) == q : forall-elim u -> q; 3
~~~

From here the other properties of $\or$ are straightforward. It is idempotent:

~~~ {.mycelium}
theorem or-idemp
* \or(q)(q) == q

proof
1. \or(\true)(\true) == \true : use or-true-l;
2. \or(\false)(\false) == \false : use or-false-false;
3. ∀u. \or(u)(u) == u
    : invoke bool-induction [P :-> \or(_)(_) == _]; 1, 2
4. \or(q)(q) == q : forall-elim u -> q; 3
~~~

$\or$ is commutative:

~~~ {.mycelium}
theorem or-comm
* \or(p)(q) == \or(q)(p)

proof
1.  \or(\true)(\true) == \or(\true)(\true) : eq-intro
2.  \or(\true)(\false) : chain
     == \true : use or-true-l;
     == \or(\false)(\true) : flop use or-false-true;
3.  ∀u. \or(\true)(u) == \or(u)(\true)
     : invoke bool-induction [P :-> \or(\true)(_) == \or(_)(\true)]; 1, 2
4.  \or(\true)(q) == \or(q)(\true) : forall-elim u -> q; 3
5.  \or(\false)(\true) : chain
     == \true : use or-false-true;
     == \or(\true)(\false) : flop use or-true-l;
6.  \or(\false)(\false) == \or(\false)(\false) : eq-intro
7.  ∀u. \or(\false)(u) == \or(u)(\false)
     : invoke bool-induction [P :-> \or(\false)(_) == \or(_)(\false)]; 5, 6
8.  \or(\false)(q) == \or(q)(\false) : forall-elim u -> q; 7
9.  ∀u. \or(u)(q) == \or(q)(u)
     : invoke bool-induction [P :-> \or(_)(q) == \or(q)(_)]; 4, 8
10. \or(p)(q) == \or(q)(p) : forall-elim u -> p; 9
~~~

And $\or$ is associative.

~~~ {.mycelium}
theorem or-assoc-l
* \or(p)(\or(q)(r)) == \or(\or(p)(q))(r)

proof
1. \or(\true)(\or(q)(r)) : chain
    == \true : use or-true-l;
    == \or(\true)(r) : flop use or-true-l;
    == \or(\or(\true)(q))(r) : flop use or-true-l; at z in \or(z)(r)
2. \or(\false)(\or(q)(r)) : chain
    == \or(q)(r) : use or-false-l;
    == \or(\or(\false)(q))(r) : flop use or-false-l; at z in \or(z)(r)
3. ∀u. \or(u)(\or(q)(r)) == \or(\or(u)(q))(r)
    : invoke bool-induction [P :-> \or(_)(\or(q)(r)) == \or(\or(_)(q))(r)]; 1, 2
4. \or(p)(\or(q)(r)) == \or(\or(p)(q))(r) : forall-elim u -> p; 3


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
1. \or(\true)(\and(q)(r)) : chain
    == \true : use or-true-l;
    == \and(\true)(\true)
        : flop use and-true-true;
    == \and(\true)(\or(\true)(r))
        : flop use or-true-l; at z in \and(\true)(z)
    == \and(\or(\true)(q))(\or(\true)(r))
        : flop use or-true-l; at z in \and(z)(\or(\true)(r))
2. \or(\false)(\and(q)(r)) : chain
    == \and(q)(r) : use or-false-l;
    == \and(q)(\or(\false)(r))
        : flop use or-false-l; at z in \and(q)(z)
    == \and(\or(\false)(q))(\or(\false)(r))
        : flop use or-false-l; at z in \and(z)(\or(\false)(r))
3. ∀u. \or(u)(\and(q)(r)) == \and(\or(u)(q))(\or(u)(r))
    : invoke bool-induction [P :-> \or(_)(\and(q)(r)) == \and(\or(_)(q))(\or(_)(r))]; 1, 2
4. \or(p)(\and(q)(r)) == \and(\or(p)(q))(\or(p)(r)) : forall-elim u -> p; 3


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
1. \and(\true)(\or(q)(r)) : chain
    == \or(q)(r) : use and-true-l;
    == \or(\and(\true)(q))(r)
        : flop use and-true-l; at z in \or(z)(r)
    == \or(\and(\true)(q))(\and(\true)(r))
        : flop use and-true-l; at z in \or(\and(\true)(q))(z)
2. \and(\false)(\or(q)(r)) : chain
    == \false : use and-false-l;
    == \or(\false)(\false) : flop use or-false-false;
    == \or(\and(\false)(q))(\false)
        : flop use and-false-l; at z in \or(z)(\false)
    == \or(\and(\false)(q))(\and(\false)(r))
        : flop use and-false-l; at z in \or(\and(\false)(q))(z)
3. ∀u. \and(u)(\or(q)(r)) == \or(\and(u)(q))(\and(u)(r))
    : invoke bool-induction [P :-> \and(_)(\or(q)(r)) == \or(\and(_)(q))(\and(_)(r))]; 1, 2
4. \and(p)(\or(q)(r)) == \or(\and(p)(q))(\and(p)(r)) : forall-elim u -> p; 3


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
