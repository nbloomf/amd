---
title: Simple Equations
---

We have enough technology now to solve some very simple equations over the natural numbers. First: the equation $$0 = 1 + n$$ has no solutions $n$.

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

We can show that $$0 = a + b$$ has only one solution, namely $a = 0$ and $b = 0$.

~~~ {.mycelium}
theorem plus-eq-zero
if
  * \plus(a)(b) == \zero
then
  * (a == \zero) /\ (b == \zero)

proof
1.    ∃k. a == \next(k) : hypothesis a-next
2.      a == \next(u) : hypothesis u
3.      \zero : chain
         == \plus(a)(b) : flop assumption 1
         == \plus(\next(u))(b) : hypothesis u at z in \plus(z)(b)
         == \next(\plus(u)(b)) : use plus-next-l;
4.      ∃k. \zero == \next(k) : exists-intro k <- \plus(u)(b); 3
5.    (a == \next(u)) => (∃k. \zero == \next(k)) : discharge u; 4
6.    ∃k. \zero == \next(k) : exists-elim u <- k; 1, 5
7.  (∃k. a == \next(k)) => (∃k. \zero == \next(k))
     : discharge a-next; 6
8.  ~(∃k. \zero == \next(k)) : use nat-disc;
9.  (∃k. a == \next(k)) => (~(∃k. \zero == \next(k))) : use simp; 8
10. ~(∃k. a == \next(k)) : use neg-intro; 7, 9
11. (a == \zero) \/ (∃k. a == \next(k)) : use nat-disj-cases-1;
13. a == \zero : use disj-syllogism-r; 11, 10
14. b : chain
     == \plus(\zero)(b) : flop use plus-zero-l;
     == \plus(a)(b) : flop use reiterate; 13 at z in \plus(z)(b)
     == \zero : assumption 1
15. (a == \zero) /\ (b == \zero) : use conj-intro; 13, 14
~~~
