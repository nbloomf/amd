---
title: Times
---

We can define $\times$ as iterated addition.

~~~ {.mycelium}
type \times :: Nat -> Nat -> Nat

rule def-times
* \times(a) == \natrec(\zero)(\plus(a))
~~~

We can characterize $\times$ as the unique solution to a system of equations.

~~~ {.mycelium}
theorem times-zero-r
* \times(a)(\zero) == \zero

proof
1. \times(a)(\zero) : chain
    == \natrec(\zero)(\plus(a))(\zero) : use def-times; at f in f(\zero)
    == \zero : use natrec-zero;


theorem times-next-r
* \times(a)(\next(b)) == \plus(a)(\times(a)(b))

proof
1. \times(a)(\next(b)) : chain
    == \natrec(\zero)(\plus(a))(\next(b)) : use def-times; at f in f(\next(b))
    == \plus(a)(\natrec(\zero)(\plus(a))(b)) : use natrec-next;
    == \plus(a)(\times(a)(b)) : flop use def-times; at f in \plus(a)(f(b))
~~~

Now $\zero$ is a left zero for $\times$:

~~~ {.mycelium}
theorem times-zero-l
* \times(\zero)(b) == \zero

proof
1.    b == \zero : hypothesis b-zero
2.    \times(\zero)(b) : chain
       == \times(\zero)(\zero)
           : hypothesis b-zero at z in \times(\zero)(z)
       == \zero : use times-zero-r;
3.  (b == \zero) => (\times(\zero)(b) == \zero)
     : discharge b-zero; 2
4.    (b == n) => (\times(\zero)(b) == \zero) : hypothesis b-n
5.    (n == n) => (\times(\zero)(n) == \zero) : sub [b :-> n]; 4
6.    n == n : eq-intro
7.    \times(\zero)(n) == \zero : use impl-elim; 6, 5
8.      b == \next(n) : hypothesis b-next
9.      \times(\zero)(b) : chain
         == \times(\zero)(\next(n))
             : hypothesis b-next at z in \times(\zero)(z)
         == \natrec(\zero)(\plus(\zero))(\next(n))
             : use def-times; at f in f(\next(n))
         == \plus(\zero)(\natrec(\zero)(\plus(\zero))(n))
             : use natrec-next;
         == \natrec(\zero)(\plus(\zero))(n) : use plus-zero-l;
         == \times(\zero)(n) : flop use def-times; at f in f(n)
         == \zero : use reiterate; 7
10.   (b == \next(n)) => (\times(\zero)(b) == \zero)
       : discharge b-next; 9
11. ((b == n) => (\times(\zero)(b) == \zero)) =>
      ((b == \next(n)) => (\times(\zero)(b) == \zero))
     : discharge b-n; 10
12. ∀k. ((b == k) => (\times(\zero)(b) == \zero)) =>
      ((b == \next(k)) => (\times(\zero)(b) == \zero))
     : forall-intro n -> k; 11
13. \times(\zero)(b) == \zero : use nat-induction; 3, 12
~~~

$\times$ interacts with $\next$ in the left argument.

~~~ {.mycelium}
theorem times-next-l
* \times(\next(a))(b) == \plus(b)(\times(a)(b))

proof
1.    b == \zero : hypothesis b-zero
2.    \times(\next(a))(b) : chain
       == \times(\next(a))(\zero) : hypothesis b-zero at z in \times(\next(a))(z)
       == \zero : use times-zero-r;
       == \times(a)(\zero) : flop use times-zero-r;
       == \plus(\zero)(\times(a)(\zero)) : flop use plus-zero-l;
       == \plus(b)(\times(a)(b)) : flop hypothesis b-zero at z in \plus(z)(\times(a)(z))
3.  (b == \zero) => (\times(\next(a))(b) == \plus(b)(\times(a)(b))) : discharge b-zero; 2
4.    (b == n) => (\times(\next(a))(b) == \plus(b)(\times(a)(b))) : hypothesis b-n
5.    (n == n) => (\times(\next(a))(n) == \plus(n)(\times(a)(n))) : sub [b :-> n]; 4
6.    n == n : eq-intro
7.    \times(\next(a))(n) == \plus(n)(\times(a)(n)) : use impl-elim; 6, 5
8.      b == \next(n) : hypothesis b-next
9.      \times(\next(a))(b) : chain
         == \times(\next(a))(\next(n)) : hypothesis b-next at z in \times(\next(a))(z)
         == \plus(\next(a))(\times(\next(a))(n)) : use times-next-r;
         == \plus(\next(a))(\plus(n)(\times(a)(n))) : use reiterate; 7 at z in \plus(\next(a))(z)
         == \plus(\plus(\next(a))(n))(\times(a)(n)) : use plus-assoc-l;
         == \plus(\plus(a)(\next(n)))(\times(a)(n)) : use plus-next; at z in \plus(z)(\times(a)(n))
         == \plus(\plus(\next(n))(a))(\times(a)(n)) : use plus-comm; at z in \plus(z)(\times(a)(n))
         == \plus(\next(n))(\plus(a)(\times(a)(n))) : use plus-assoc-r;
         == \plus(\next(n))(\times(a)(\next(n))) : flop use times-next-r; at z in \plus(\next(n))(z)
         == \plus(b)(\times(a)(b)) : flop hypothesis b-next at z in \plus(z)(\times(a)(z))
10.   (b == \next(n)) => (\times(\next(a))(b) == \plus(b)(\times(a)(b))) : discharge b-next; 9
11. ((b == n) => \times(\next(a))(b) == \plus(b)(\times(a)(b))) =>
      ((b == \next(n)) => \times(\next(a))(b) == \plus(b)(\times(a)(b))) : discharge b-n; 10
12. ∀k. ((b == k) => \times(\next(a))(b) == \plus(b)(\times(a)(b))) =>
      ((b == \next(k)) => \times(\next(a))(b) == \plus(b)(\times(a)(b))) : forall-intro n -> k; 11
13. \times(\next(a))(b) == \plus(b)(\times(a)(b)) : use nat-induction; 3, 12
~~~

$\times$ is commutative.

~~~ {.mycelium}
theorem times-comm
* \times(a)(b) == \times(b)(a)

proof
1.    b == \zero : hypothesis b-zero
2.    \times(a)(b) : chain
       == \times(a)(\zero) : hypothesis b-zero at z in \times(a)(z)
       == \zero : use times-zero-r;
       == \times(\zero)(a) : flop use times-zero-l;
       == \times(b)(a) : flop hypothesis b-zero at z in \times(z)(a)
3. (b == \zero) => (\times(a)(b) == \times(b)(a)) : discharge b-zero; 2
4.    (b == n) => (\times(a)(b) == \times(b)(a)) : hypothesis b-n
5.    (n == n) => (\times(a)(n) == \times(n)(a)) : sub [b :-> n]; 4
6.    n == n : eq-intro
7.    \times(a)(n) == \times(n)(a) : use impl-elim; 6, 5
8.      b == \next(n) : hypothesis b-next
9.      \times(a)(b) : chain
         == \times(a)(\next(n)) : hypothesis b-next at z in \times(a)(z)
         == \plus(a)(\times(a)(n)) : use times-next-r;
         == \plus(a)(\times(n)(a)) : use reiterate; 7 at z in \plus(a)(z)
         == \times(\next(n))(a) : flop use times-next-l;
         == \times(b)(a) : flop hypothesis b-next at z in \times(z)(a)
10.   (b == \next(n)) => (\times(a)(b) == \times(b)(a)) : discharge b-next; 9
11. ((b == n) => (\times(a)(b) == \times(b)(a))) =>
      ((b == \next(n)) => (\times(a)(b) == \times(b)(a))) : discharge b-n; 10
12. ∀k. ((b == k) => (\times(a)(b) == \times(b)(a))) =>
      ((b == \next(k)) => (\times(a)(b) == \times(b)(a))) : forall-intro n -> k; 11
13. \times(a)(b) == \times(b)(a) : use nat-induction; 3, 12
~~~

~~~ {.mycelium}
theorem times-plus-dist-l
* \times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c))

proof
1.    c == \zero : hypothesis c-zero
2.    \times(a)(\plus(b)(c)) : chain
       == \times(a)(\plus(b)(\zero)) : hypothesis c-zero at z in \times(a)(\plus(b)(z))
       == \times(a)(b) : use plus-zero-r; at z in \times(a)(z)
       == \plus(\times(a)(b))(\zero) : flop use plus-zero-r;
       == \plus(\times(a)(b))(\times(a)(\zero)) : flop use times-zero-r; at z in \plus(\times(a)(b))(z)
       == \plus(\times(a)(b))(\times(a)(c)) : flop hypothesis c-zero at z in \plus(\times(a)(b))(\times(a)(z))
3. (c == \zero) => (\times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c))) : discharge c-zero; 2
4.   (c == n) => (\times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c))) : hypothesis c-n
5.   (n == n) => (\times(a)(\plus(b)(n)) == \plus(\times(a)(b))(\times(a)(n))) : sub [c :-> n]; 4
6.   n == n : eq-intro
7.   \times(a)(\plus(b)(n)) == \plus(\times(a)(b))(\times(a)(n)) : use impl-elim; 6, 5
8.   \times(a)(\plus(\next(b))(n)) == \plus(\times(a)(\next(b)))(\times(a)(n)) : sub [b :-> \next(b)]; 7
9.     c == \next(n) : hypothesis c-next
10.    \times(a)(\plus(b)(c)) : chain
        == \times(a)(\plus(b)(\next(n))) : hypothesis c-next at z in \times(a)(\plus(b)(z))
        == \times(a)(\plus(\next(b))(n)) : flop use plus-next; at z in \times(a)(z)
        == \plus(\times(a)(\next(b)))(\times(a)(n)) : use reiterate; 8
        == \plus(\plus(a)(\times(a)(b)))(\times(a)(n)) : use times-next-r; at z in \plus(z)(\times(a)(n))
        == \plus(\plus(\times(a)(b))(a))(\times(a)(n)) : use plus-comm; at z in \plus(z)(\times(a)(n))
        == \plus(\times(a)(b))(\plus(a)(\times(a)(n))) : use plus-assoc-r;
        == \plus(\times(a)(b))(\times(a)(\next(n))) : flop use times-next-r; at z in \plus(\times(a)(b))(z)
        == \plus(\times(a)(b))(\times(a)(c)) : flop hypothesis c-next at z in \plus(\times(a)(b))(\times(a)(z))
11.   (c == \next(n)) => (\times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c))) : discharge c-next; 10
12. ((c == n) => (\times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c)))) =>
      ((c == \next(n)) => (\times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c)))) : discharge c-n; 11
13. ∀k. ((c == k) => (\times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c)))) =>
      ((c == \next(k)) => (\times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c)))) : forall-intro n -> k; 12
14. \times(a)(\plus(b)(c)) == \plus(\times(a)(b))(\times(a)(c)) : use nat-induction; 3, 13
~~~

$\times$ is associative.

~~~ {.mycelium}
theorem times-assoc-l
* \times(a)(\times(b)(c)) == \times(\times(a)(b))(c)

proof
1.    c == \zero : hypothesis c-zero
2.    \times(a)(\times(b)(c)) : chain
       == \times(a)(\times(b)(\zero)) : hypothesis c-zero at z in \times(a)(\times(b)(z))
       == \times(a)(\zero) : use times-zero-r; at z in \times(a)(z)
       == \zero : use times-zero-r;
       == \times(\times(a)(b))(\zero) : flop use times-zero-r;
       == \times(\times(a)(b))(c) : flop hypothesis c-zero at z in \times(\times(a)(b))(z)
3. (c == \zero) => (\times(a)(\times(b)(c)) == \times(\times(a)(b))(c)) : discharge c-zero; 2
4.   (c == n) => (\times(a)(\times(b)(c)) == \times(\times(a)(b))(c)) : hypothesis c-n
5.   (n == n) => (\times(a)(\times(b)(n)) == \times(\times(a)(b))(n)) : sub [c :-> n]; 4
6.   n == n : eq-intro
7.   \times(a)(\times(b)(n)) == \times(\times(a)(b))(n) : use impl-elim; 6, 5
8.     c == \next(n) : hypothesis c-next
9.     \times(a)(\times(b)(c)) : chain
        == \times(a)(\times(b)(\next(n))) : hypothesis c-next at z in \times(a)(\times(b)(z))
        == \times(a)(\plus(b)(\times(b)(n))) : use times-next-r; at z in \times(a)(z)
        == \plus(\times(a)(b))(\times(a)(\times(b)(n))) : use times-plus-dist-l;
        == \plus(\times(a)(b))(\times(\times(a)(b))(n)) : use reiterate; 7 at z in \plus(\times(a)(b))(z)
        == \times(\times(a)(b))(\next(n)) : flop use times-next-r;
        == \times(\times(a)(b))(c) : flop hypothesis c-next at z in \times(\times(a)(b))(z)
10.   (c == \next(n)) => (\times(a)(\times(b)(c)) == \times(\times(a)(b))(c)) : discharge c-next; 9
11. ((c == n) => (\times(a)(\times(b)(c)) == \times(\times(a)(b))(c))) =>
      ((c == \next(n)) => (\times(a)(\times(b)(c)) == \times(\times(a)(b))(c))) : discharge c-n; 10
12. ∀k. ((c == k) => (\times(a)(\times(b)(c)) == \times(\times(a)(b))(c))) =>
      ((c == \next(k)) => (\times(a)(\times(b)(c)) == \times(\times(a)(b))(c))) : forall-intro n -> k; 11
13. \times(a)(\times(b)(c)) == \times(\times(a)(b))(c) : use nat-induction; 3, 12


theorem times-assoc-r
* \times(\times(a)(b))(c) == \times(a)(\times(b)(c))

proof
1. \times(a)(\times(b)(c)) == \times(\times(a)(b))(c) : use times-assoc-l;
2. \times(\times(a)(b))(c) == \times(a)(\times(b)(c)) : use eq-sym; 1
~~~

$\next(\zero)$ is neutral for $\times.

~~~ {.mycelium}
theorem times-one-r
* \times(a)(\next(\zero)) == a

proof
1. \times(a)(\next(\zero)) : chain
    == \plus(a)(\times(a)(\zero)) : use times-next-r;
    == \plus(a)(\zero) : use times-zero-r; at z in \plus(a)(z)
    == a : use plus-zero-r;


theorem times-one-l
* \times(\next(\zero))(a) == a

proof
1. \times(\next(\zero))(a) : chain
    == \times(a)(\next(\zero)) : use times-comm;
    == a : use times-one-r;
~~~

And $\times$ is _almost_ cancellative.

~~~ {.mycelium}
theorem times-cancel-r
if
  * \times(a)(\next(c)) == \times(b)(\next(c))
then
  * a == b

proof
1.    c == \zero : hypothesis c-zero
2.    a : chain
       == \times(a)(\next(\zero)) : flop use times-one-r;
       == \times(a)(\next(c)) : flop hypothesis c-zero at z in \times(a)(\next(z))
       == \times(b)(\next(c)) : assumption 1
       == \times(b)(\next(\zero)) : hypothesis c-zero at z in \times(b)(\next(z))
       == b : use times-one-r;
3.  (c == \zero) => (a == b) : discharge c-zero; 2
4.    (c == n) => (a == b) : hypothesis c-n
5.    (n == n) => (a == b) : sub [c :-> n]; 4
6.    n == n : eq-intro
7.      c == \next(n) : hypothesis c-next
8.      a == b : use impl-elim; 6, 5
9.      (c == \next(n)) /\ (a == b) : use conj-intro; 7, 8
10.     a == b : use conj-elim-r; 9
11.   (c == \next(n)) => (a == b) : discharge c-next; 10
12. ((c == n) => (a == b)) => ((c == \next(n)) => (a == b)) : discharge c-n; 11
13. ∀k. ((c == k) => (a == b)) => ((c == \next(k)) => (a == b)) : forall-intro n -> k; 12
14. a == b : use nat-induction; 3, 13


theorem times-cancel-l
if
  * \times(\next(c))(a) == \times(\next(c))(b)
then
  * a == b

proof
1. \times(a)(\next(c)) : chain
    == \times(\next(c))(a) : use times-comm;
    == \times(\next(c))(b) : assumption 1
    == \times(b)(\next(c)) : use times-comm;
2. a == b : use times-cancel-r; 1
~~~
