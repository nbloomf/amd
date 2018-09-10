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
  * (q == \true) => P
  * (q == \false) => P
then
  * P
~~~

~~~ {.mycelium}
theorem bool-cases
* (q == \true) \/ (q == \false)

proof
1.   q == \true : hypothesis T
2.   (q == \true) \/ (q == \false) : use disj-intro-l; 1
3. (q == \true) => ((q == \true) \/ (q == \false)) : discharge T; 2
4.   q == \false : hypothesis F
5.   (q == \true) \/ (q == \false) : use disj-intro-r; 4
6. (q == \false) => ((q == \true) \/ (q == \false)) : discharge F; 5
7. (q == \true) \/ (q == \false) : use bool-induction; 3, 6
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
