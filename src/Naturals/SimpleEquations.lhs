---
title: Simple Equations
---

We have enough technology now to solve some very simple equations over the natural numbers. First: the equation $$0 = 1 + n$$ has no solutions.

~~~ {.mycelium}
theorem zero-not-one-plus
* ~(∃n. \zero == \plus(\next(\zero))(n))

proof
1.    ∃n. \zero == \plus(\next(\zero))(n) : hypothesis t
2.      \zero == \plus(\next(\zero))(u) : hypothesis u
3.      \zero : chain
         == \plus(\next(\zero))(u) : hypothesis u
         == \next(\plus(\zero)(u)) : use plus-next-l;
         == \next(u) : use plus-zero-l; at z in \next(z)
4.      ∃n. \zero == \next(n) : exists-intro n <- u; 3
5.    (\zero == \plus(\next(\zero))(u)) =>
        (∃n. \zero == \next(n)) : discharge u; 4
6.    ∃n. \zero == \next(n) : exists-elim u <- n; 1, 5
7.  (∃n. \zero == \plus(\next(\zero))(n)) =>
      (∃n. \zero == \next(n)) : discharge t; 6
8.  ~(∃n. \zero == \next(n)) : use nat-disc;
9.  (∃n. \zero == \plus(\next(\zero))(n)) =>
      (~(∃n. \zero == \next(n))) : use simp; 8
10. ~(∃n. \zero == \plus(\next(\zero))(n)) : use neg-intro; 7, 9
~~~

 ~~~ {.mycelium}
theorem plus-eq-zero
if
  * \plus(a)(b) == \zero
then
  * (a == \zero) /\ (b == \zero)

proof
1.    b == \zero : hypothesis b-zero
2.    a : chain
       == \plus(a)(\zero) : flop use plus-zero-r;
       == \plus(a)(b) : flop hypothesis b-zero at z in \plus(a)(z)
       == \zero : assumption 1
3.    (a == \zero) /\ (b == \zero) : use conj-intro; 2, 1
4.  (b == \zero) => ((a == \zero) /\ (b == \zero)) : discharge b-zero; 3
5.    (b == n) => ((a == \zero) /\ (b == \zero)) : hypothesis b-n
6.    
 ~~~
