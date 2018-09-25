---
title: Booleans
---

We can represent booleans as a type with exactly two values.

~~~ {.mycelium}
type \true :: Bool

type \false :: Bool

rule bool-disc
* ~(\true == \false)
~~~

A special function $\if$ lets us discriminate based on a boolean value.

~~~ {.mycelium}
type \if :: a -> a -> Bool -> a
~~~

Now $\if$ is a homomorphism:

~~~ {.mycelium}
rule if-true
* \if(x)(y)(\true) == x

rule if-false
* \if(x)(y)(\false) == y
~~~

And is unique.

~~~ {.mycelium}
rule if-unique
if
  * t(\true) == x
  * t(\false) == y
then
  * t == \if(x)(y)
~~~

Finally, we have an induction principle for $\Bool$.

~~~ {.mycelium}
rule bool-induction
if
  * P[_ :-> \true]
  * P[_ :-> \false]
then
  * ∀u. P[_ :-> u]
~~~

~~~ {.mycelium}
theorem bool-cases
* (q == \true) \/ (q == \false)

proof
1. \true == \true : eq-intro
2. (\true == \true) \/ (\true == \false)
    : use disj-intro-l; 1
3. \false == \false : eq-intro
4. (\false == \true) \/ (\false == \false)
    : use disj-intro-r; 3
5. ∀u. (u == \true) \/ (u == \false)
    : invoke bool-induction [P :-> (_ == \true) \/ (_ == \false)]; 2, 4
6. (q == \true) \/ (q == \false)
    : forall-elim u -> q; 5
~~~

$\Bool$ is the first concrete type we've seen, and there's a lot to say about it, so we'll split it up over several sections. First, like the other inductive types, we can characterize $\id$ in terms of the universal arrow.

~~~ {.mycelium}
theorem if-true-false
* \id == \if(\true)(\false)

proof
1. \id(\true) == \true : use def-id;
2. \id(\false) == \false : use def-id;
3. \id == \if(\true)(\false) : use if-unique; 1, 2
~~~

We can also characterize $\const$ as an $\if$.

~~~ {.mycelium}
theorem if-const
* \const(a) == \if(a)(a)

proof
1. \const(a)(\true) == a : use def-const;
2. \const(a)(\false) == a : use def-const;
3. \const(a) == \if(a)(a) : use if-unique; 1, 2
~~~

~~~ {.mycelium}
theorem not-eq-true
if
  * ~(q == \true)
then
  * q == \false

proof
1. (q == \true) \/ (q == \false) : use bool-cases;
2. ~(q == \true) : assumption 1
3. q == \false : use disj-syllogism-l; 1, 2


theorem not-eq-false
if
  * ~(q == \false)
then
  * q == \true

proof
1. (q == \true) \/ (q == \false) : use bool-cases;
2. ~(q == \false) : assumption 1
3. q == \true : use disj-syllogism-r; 1, 2
~~~

~~~ {.mycelium}
theorem if-ap
* \if(f(a))(f(b))(p) == f(\if(a)(b)(p))

proof
1. \if(f(a))(f(b))(\true) : chain
    == f(a) : use if-true;
    == f(\if(a)(b)(\true))
     : flop use if-true; at z in f(z)

2. \if(f(a))(f(b))(\false) : chain
    == f(b) : use if-false;
    == f(\if(a)(b)(\false))
     : flop use if-false; at z in f(z)

3. ∀u. \if(f(a))(f(b))(u) == f(\if(a)(b)(u))
    : invoke bool-induction
      [P :-> \if(f(a))(f(b))(_) == f(\if(a)(b)(_))]; 1, 2

4. \if(f(a))(f(b))(p) == f(\if(a)(b)(p))
    : forall-elim u -> p; 3
~~~

~~~ {.mycelium}
theorem equiv-true-eq
if
  * (p == \true) <=> (q == \true)
then
  * p == q

proof
1.  (p == \true) <=> (q == \true)
     : assumption 1

2.  (p == \true) \/ (p == \false)
     : use bool-cases;

3.    p == \true : hypothesis p-t

4.    (p == \true) => (q == \true)
       : use equiv-elim-r; 1

5.    q == \true : use impl-elim; 3, 4

6.    p : chain
       == \true : hypothesis p-t
       == q : flop use reiterate; 5

7.  (p == \true) => (p == q)
     : discharge p-t; 6

8.    p == \false : hypothesis p-f

9.      q == \true : hypothesis q-t

10.     (q == \true) => (p == \true)
         : use equiv-elim-l; 1

11.     p == \true : use impl-elim; 9, 10

12.     \true : chain
         == p : flop use reiterate; 11
         == \false : hypothesis p-f

13.   (q == \true) => (\true == \false)
       : discharge q-t; 12

14.   ~(\true == \false)
       : use bool-disc;

15.   ~(q == \true) : use modus-tollens; 13, 14

16.   q == \false : use not-eq-true; 15

17.   p : chain
       == \false : hypothesis p-f
       == q : flop use reiterate; 16

18. (p == \false) => (p == q)
     : discharge p-f; 17

19. p == q
     : use disj-elim; 2, 7, 18
~~~
