---
title: Equivalence
---

The last of the logical rules of inference are the rules for $\Leftrightarrow$. These are pretty boring.

~~~ {.mycelium}
rule equiv-intro
if
  * P => Q
  * Q => P
then
  * P <=> Q

rule equiv-elim-r
if
  * P <=> Q
then
  * P => Q

rule equiv-elim-l
if
  * P <=> Q
then
  * Q => P
~~~

We won't need to use equivalence a ton, but here are some basic properties anyway.

~~~ {.mycelium}
theorem equiv-refl
* P <=> P

proof
1. P => P : use impl-idemp;
2. P <=> P : use equiv-intro; 1, 1
~~~

It is symmetric:

~~~ {.mycelium}
theorem equiv-sym
if
  * P <=> Q
then
  * Q <=> P

proof
1. P <=> Q : assumption 1
2. P => Q : use equiv-elim-r; 1
3. Q => P : use equiv-elim-l; 1
4. Q <=> P : use equiv-intro; 3, 2
~~~

And it is transitive.

~~~ {.mycelium}
theorem equiv-trans
if
  * P <=> Q
  * Q <=> R
then
  * P <=> R

proof
1. P <=> Q : assumption 1
2. Q <=> R : assumption 2
3. P => Q : use equiv-elim-r; 1
4. Q => R : use equiv-elim-r; 2
5. P => R : use syllogism; 3, 4
6. R => Q : use equiv-elim-l; 2
7. Q => P : use equiv-elim-l; 1
8. R => P : use syllogism; 6, 7
9. P <=> R : use equiv-intro; 5, 8


theorem equiv-trans-3
if
  * P <=> Q
  * Q <=> R
  * R <=> S
then
  * P <=> S

proof
1. P <=> Q : assumption 1
2. Q <=> R : assumption 2
3. P <=> R : use equiv-trans; 1, 2
4. R <=> S : assumption 3
5. P <=> S : use equiv-trans; 3, 4
~~~

~~~ {.mycelium}
theorem eq-sym-equiv
* (a == b) <=> (b == a)

proof
1.   a == b : hypothesis one
2.   b == a : use eq-sym; 1
3. (a == b) => (b == a)
    : discharge one; 2
4.   b == a : hypothesis two
5.   a == b : use eq-sym; 4
6. (b == a) => (a == b)
    : discharge two; 5
7. (a == b) <=> (b == a)
    : use equiv-intro; 3, 6
~~~
