---
title: Not
---

Next we define boolean $\not$.

~~~ {.mycelium}
type \not :: Bool -> Bool

definition def-not
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
1. \comp(\not)(\not)(\true) : chain
    == \not(\not(\true)) : use def-comp;
    == \not(\false) : use not-true; at z in \not(z)
    == \true : use not-false;
    == \id(\true) : flop use def-id;
2. \comp(\not)(\not)(\false) : chain
    == \not(\not(\false)) : use def-comp;
    == \not(\true) : use not-false; at z in \not(z)
    == \false : use not-true;
    == \id(\false) : flop use def-id;
3. ∀u. \comp(\not)(\not)(u) == \id(u)
    : invoke bool-induction [P :-> \comp(\not)(\not)(_) == \id(_)]; 1, 2
4. \comp(\not)(\not) == \id
    : use fun-eq; 3
~~~

And we have DeMorgan's laws: $\not$ distributes over $\or$ (kind of):

~~~ {.mycelium}
theorem not-or
* \not(\or(p)(q)) == \and(\not(p))(\not(q))

proof
1. \not(\or(\true)(q)) : chain
    == \not(\true) : use or-true-l; at z in \not(z)
    == \false : use not-true;
    == \and(\false)(\not(q)) : flop use and-false-l;
    == \and(\not(\true))(\not(q)) : flop use not-true; at z in \and(z)(\not(q))
2. \not(\or(\false)(q)) : chain
    == \not(q) : use or-false-l; at z in \not(z)
    == \and(\true)(\not(q)) : flop use and-true-l;
    == \and(\not(\false))(\not(q)) : flop use not-false; at z in \and(z)(\not(q))
3. ∀u. \not(\or(u)(q)) == \and(\not(u))(\not(q))
    : invoke bool-induction [P :-> \not(\or(_)(q)) == \and(\not(_))(\not(q))]; 1, 2
4. \not(\or(p)(q)) == \and(\not(p))(\not(q)) : forall-elim u -> p; 3
~~~

And $\not$ distributes over $\and$ (kind of).

~~~ {.mycelium}
theorem not-and
* \not(\and(p)(q)) == \or(\not(p))(\not(q))

proof
1. \not(\and(\true)(q)) : chain
    == \not(q) : use and-true-l; at z in \not(z)
    == \or(\false)(\not(q)) : flop use or-false-l;
    == \or(\not(\true))(\not(q))
        : flop use not-true; at z in \or(z)(\not(q))
2. \not(\and(\false)(q)) : chain
    == \not(\false) : use and-false-l; at z in \not(z)
    == \true : use not-false;
    == \or(\true)(\not(q))
        : flop use or-true-l;
    == \or(\not(\false))(\not(q))
        : flop use not-false; at z in \or(z)(\not(q))
3. ∀u. \not(\and(u)(q)) == \or(\not(u))(\not(q))
    : invoke bool-induction [P :-> \not(\and(_)(q)) == \or(\not(_))(\not(q))]; 1, 2
4. \not(\and(p)(q)) == \or(\not(p))(\not(q))
    : forall-elim u -> p; 3
~~~
