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

The same is true of $$0 = a + b.$$

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

We can also show that $ab = \next(\zero)$ has only one solution, namely $a == \next(\zero), b = \next(\zero)$.

~~~ {.mycelium}
theorem times-eq-one
if
  * \times(a)(b) == \next(\zero)
then
  * (a == \next(\zero)) /\ (b == \next(\zero))

proof
1.    \times(a)(b) == \next(\zero)
       : hypothesis one

2.    (a == \zero) \/ (∃k. a == \next(k))
       : use nat-disj-cases-1;

3.      a == \zero
         : hypothesis a-zero

4.      \zero : chain
         == \times(\zero)(b)
          : flop use times-zero-l;
         == \times(a)(b)
          : flop hypothesis a-zero at z in
            \times(z)(b)
         == \next(\zero)
          : hypothesis one

5.      ∃k. \zero == \next(k)
         : exists-intro k <- \zero; 4

6.    (a == \zero) => (∃k. \zero == \next(k))
       : discharge a-zero; 5

7.    ~(∃k. \zero == \next(k))
       : use nat-disc;

8.    ~(a == \zero)
       : use modus-tollens; 6, 7

9.    ∃k. a == \next(k)
       : use disj-syllogism-l; 2, 8

10.     a == \next(u)
         : hypothesis a-next-u

11.     (b == \zero) \/ (∃k. b == \next(k))
         : use nat-disj-cases-1;

12.       b == \zero
           : hypothesis b-zero

13.       \zero : chain
           == \times(a)(\zero)
            : flop use times-zero-r;
           == \times(a)(b)
            : flop hypothesis b-zero at z in
              \times(a)(z)
           == \next(\zero)
            : hypothesis one

14.       ∃k. \zero == \next(k)
           : exists-intro k <- \zero; 13

15.     (b == \zero) => (∃k. \zero == \next(k))
         : discharge b-zero; 14

16.      ~(∃k. \zero == \next(k))
         : use nat-disc;

17.      ~(b == \zero)
         : use modus-tollens; 15, 16

18.      ∃k. b == \next(k)
         : use disj-syllogism-l; 11, 17

19.        b == \next(v)
            : hypothesis b-next-v

20.        (v == \zero) \/ (∃k. v == \next(k))
            : use nat-disj-cases-1;

21.          ∃k. v == \next(k)
              : hypothesis v-next

22.            v == \next(w)
                : hypothesis v-next-w

23.            \next(\zero) : chain
                == \times(a)(b)
                 : flop assumption 1
                == \times(a)(\next(v))
                 : hypothesis b-next-v at z in
                   \times(a)(z)
                == \times(a)(\next(\next(w)))
                 : hypothesis v-next-w at z in
                 \times(a)(\next(z))
                == \times(\next(u))(\next(\next(w)))
                 : hypothesis a-next-u at z in
                   \times(z)(\next(\next(w)))
                == \plus(\next(\next(w)))(\times(u)(\next(\next(w))))
                 : use times-next-l;
                == \next(\plus(\next(w))(\times(u)(\next(\next(w)))))
                 : use plus-next-l;
                == \next(\next(\plus(w)(\times(u)(\next(\next(w))))))
                 : use plus-next-l; at z in
                   \next(z)

24.            \zero == \next(\plus(w)(\times(u)(\next(\next(w)))))
                : use next-inj; 23

25.            ∃k. \zero == \next(k)
                : exists-intro k <- \plus(w)(\times(u)(\next(\next(w)))); 24

26.          (v == \next(w)) => (∃k. \zero == \next(k))
              : discharge v-next-w; 25

27.          ∃k. \zero == \next(k)
              : exists-elim w <- k; 21, 26

28.        (∃k. v == \next(k)) => (∃k. \zero == \next(k))
            : discharge v-next; 27

29.        ~(∃k. v == \next(k))
            : use modus-tollens; 28, 7

30.        v == \zero
            : use disj-syllogism-r; 20, 29

31.        b : chain
            == \next(v)
             : hypothesis b-next-v
            == \next(\zero)
             : use reiterate; 30 at z in
               \next(z)

32.      (b == \next(v)) => (b == \next(\zero))
          : discharge b-next-v; 31

33.      b == \next(\zero)
          : exists-elim v <- k; 18, 32

34.   (a == \next(u)) => (b == \next(\zero))
       : discharge a-next-u; 33

35.   b == \next(\zero)
       : exists-elim u <- k; 9, 34

36.   a : chain
       == \times(a)(\next(\zero))
        : flop use times-one-r;
       == \times(a)(b)
        : flop use reiterate; 35 at z in
          \times(a)(z)
       == \next(\zero)
        : hypothesis one

37.   (a == \next(\zero)) /\ (b == \next(\zero))
       : use conj-intro; 36, 35

38. (\times(a)(b) == \next(\zero)) => ((a == \next(\zero)) /\ (b == \next(\zero)))
     : discharge one; 37

39. \times(a)(b) == \next(\zero)
     : assumption 1

40. (a == \next(\zero)) /\ (b == \next(\zero))
     : use impl-elim; 39, 38
~~~
