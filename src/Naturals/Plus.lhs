---
title: Plus
---

We can define $\plus$ on natural numbers in terms of $\natrec$.

~~~ {.mycelium}
type \plus :: Nat -> Nat -> Nat

definition def-plus
* \plus(a)(b) == \natrec(a)(\next)(b)
~~~

And we can characterize $\plus$ as the unique solution to a system of defining equations.

~~~ {.mycelium}
theorem plus-unique
if
  * t(a)(\zero) == a
  * \comp(t(a))(\next) == \comp(\next)(t(a))
then
  * t(a) == \plus(a)

proof
1. t(a)(\zero) == a : assumption 1
2. \comp(t(a))(\next) == \comp(\next)(t(a)) : assumption 2
3. t(a) == \natrec(a)(\next) : use natrec-unique; 1, 2
4. t(a)(b) : chain
    == \natrec(a)(\next)(b) : use fun-ap; 3
    == \plus(a)(b) : flop use def-plus;
5. ∀k. t(a)(k) == \plus(a)(k) : forall-intro b -> k; 4
6. t(a) == \plus(a) : use fun-eq; 5
~~~

$\zero$ is a left identity for $\plus$.

~~~ {.mycelium}
theorem plus-zero-l
* \plus(\zero)(a) == a

proof
1. \plus(\zero)(a) : chain
    == \natrec(\zero)(\next)(a) : use def-plus;
    == \id(a) : flop use natrec-zero-next; at f in f(a)
    == a : use def-id;
~~~

$\zero$ is a right identity for plus.

~~~ {.mycelium}
theorem plus-zero-r
* \plus(a)(\zero) == a

proof
1. \plus(a)(\zero) : chain
    == \natrec(a)(\next)(\zero) : use def-plus;
    == a : use natrec-zero;
~~~

We can pull $\next$ out of the right argument of $\plus$.

~~~ {.mycelium}
theorem plus-next-r
* \plus(a)(\next(b)) == \next(\plus(a)(b))

proof
1. \plus(a)(\next(b)) : chain
    == \natrec(a)(\next)(\next(b)) : use def-plus;
    == \next(\natrec(a)(\next)(b)) : use natrec-next;
    == \next(\plus(a)(b)) : flop use def-plus; at z in \next(z)
~~~

We can pull $\next$ out of the left argument of $\plus$.

~~~ {.mycelium}
theorem plus-next-l
* \plus(\next(a))(b) == \next(\plus(a)(b))

proof
1.    b == \zero : hypothesis zero
2.    \plus(\next(a))(b) : chain
       == \plus(\next(a))(\zero)
           : hypothesis zero at z in \plus(\next(a))(z)
       == \next(a) : use plus-zero-r;
       == \next(\plus(a)(\zero))
           : flop use plus-zero-r; at z in \next(z)
       == \next(\plus(a)(b))
           : flop hypothesis zero at z in \next(\plus(a)(z))
3.  (b == \zero) => (\plus(\next(a))(b) == \next(\plus(a)(b)))
     : discharge zero; 2
4.    (b == n) => (\plus(\next(a))(b) == \next(\plus(a)(b)))
       : hypothesis n
5.    (n == n) => (\plus(\next(a))(n) == \next(\plus(a)(n)))
       : sub [b :-> n]; 4
6.    n == n : eq-intro
7.    \plus(\next(a))(n) == \next(\plus(a)(n)) : use impl-elim; 6, 5
8.      b == \next(n) : hypothesis next
9.      \plus(\next(a))(b) : chain
         == \plus(\next(a))(\next(n))
             : hypothesis next at z in \plus(\next(a))(z)
         == \next(\plus(\next(a))(n)) : use plus-next-r;
         == \next(\next(\plus(a)(n))) : use ap-eq; 7
         == \next(\plus(a)(\next(n)))
             : flop use plus-next-r; at z in \next(z)
         == \next(\plus(a)(b))
             : flop hypothesis next at z in \next(\plus(a)(z))
10.   (b == \next(n)) => (\plus(\next(a))(b) == \next(\plus(a)(b)))
       : discharge next; 9
11. ((b == n) => (\plus(\next(a))(b) == \next(\plus(a)(b)))) =>
      ((b == \next(n)) => (\plus(\next(a))(b) == \next(\plus(a)(b))))
     : discharge n; 10
12. ∀k. ((b == k) => (\plus(\next(a))(b) == \next(\plus(a)(b)))) =>
      ((b == \next(k)) => (\plus(\next(a))(b) == \next(\plus(a)(b))))
     : forall-intro n -> k; 11
13. \plus(\next(a))(b) == \next(\plus(a)(b)) : use nat-induction; 3, 12
~~~

We can move $\next$ from one argument to the other inside $\plus$.

~~~ {.mycelium}
theorem plus-next
* \plus(\next(a))(b) == \plus(a)(\next(b))

proof
1. \plus(\next(a))(b) : chain
    == \next(\plus(a)(b)) : use plus-next-l;
    == \plus(a)(\next(b)) : flop use plus-next-r;
~~~

$\plus$ is commutative.

~~~ {.mycelium}
theorem plus-comm
* \plus(a)(b) == \plus(b)(a)

proof
1.    a == \zero : hypothesis zero
2.    \plus(a)(b) : chain
       == \plus(\zero)(b) : hypothesis zero at z in \plus(z)(b)
       == b : use plus-zero-l;
       == \plus(b)(\zero) : flop use plus-zero-r;
       == \plus(b)(a) : flop hypothesis zero at z in \plus(b)(z)
3.  (a == \zero) => (\plus(a)(b) == \plus(b)(a)) : discharge zero; 2
4.    (a == n) => (\plus(a)(b) == \plus(b)(a)) : hypothesis n
5.    (n == n) => (\plus(n)(b) == \plus(b)(n)) : sub [a :-> n]; 4
6.    n == n : eq-intro
7.    \plus(n)(b) == \plus(b)(n) : use impl-elim; 6, 5
8.      a == \next(n) : hypothesis next
9.      \plus(a)(b) : chain
         == \plus(\next(n))(b) : hypothesis next at z in \plus(z)(b)
         == \next(\plus(n)(b)) : use plus-next-l;
         == \next(\plus(b)(n)) : use ap-eq; 7
         == \plus(b)(\next(n)) : flop use plus-next-r;
         == \plus(b)(a) : flop hypothesis next at z in \plus(b)(z)
10.   (a == \next(n)) => (\plus(a)(b) == \plus(b)(a))
       : discharge next; 9
11. ((a == n) => (\plus(a)(b) == \plus(b)(a))) =>
      ((a == \next(n)) => (\plus(a)(b) == \plus(b)(a)))
     : discharge n; 10
12. ∀k. ((a == k) => (\plus(a)(b) == \plus(b)(a))) =>
      ((a == \next(k)) => (\plus(a)(b) == \plus(b)(a)))
     : forall-intro n -> k; 11
13. \plus(a)(b) == \plus(b)(a) : use nat-induction; 3, 12
~~~

$\plus$ is associative.

~~~ {.mycelium}
theorem plus-assoc-l
* \plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c)

proof
1.    c == \zero : hypothesis c-zero
2.    \plus(a)(\plus(b)(c)) : chain
       == \plus(a)(\plus(b)(\zero))
           : hypothesis c-zero at z in \plus(a)(\plus(b)(z))
       == \plus(a)(b) : use plus-zero-r; at z in \plus(a)(z)
       == \plus(\plus(a)(b))(\zero) : flop use plus-zero-r;
       == \plus(\plus(a)(b))(c)
           : flop hypothesis c-zero at z in \plus(\plus(a)(b))(z)
3.  (c == \zero) => (\plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c))
     : discharge c-zero; 2
4.    (c == n) => (\plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c))
       : hypothesis c-n
5.    (n == n) => (\plus(a)(\plus(b)(n)) == \plus(\plus(a)(b))(n))
       : sub [c :-> n]; 4
6.    n == n : eq-intro
7.    \plus(a)(\plus(b)(n)) == \plus(\plus(a)(b))(n)
       : use impl-elim; 6, 5
8.      c == \next(n) : hypothesis c-next
9.      \plus(a)(\plus(b)(c)) : chain
         == \plus(a)(\plus(b)(\next(n)))
             : hypothesis c-next at z in \plus(a)(\plus(b)(z))
         == \plus(a)(\next(\plus(b)(n)))
             : use plus-next-r; at z in \plus(a)(z)
         == \next(\plus(a)(\plus(b)(n)))
             : use plus-next-r;
         == \next(\plus(\plus(a)(b))(n)) : use ap-eq; 7
         == \plus(\plus(a)(b))(\next(n)) : flop use plus-next-r;
         == \plus(\plus(a)(b))(c)
             : flop hypothesis c-next at z in \plus(\plus(a)(b))(z)
10.   (c == \next(n)) => (\plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c))
       : discharge c-next; 9
11. ((c == n) => (\plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c))) =>
      ((c == \next(n)) => (\plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c)))
     : discharge c-n; 10
12. ∀k. ((c == k) => (\plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c))) =>
      ((c == \next(k)) => (\plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c)))
     : forall-intro n -> k; 11
13. \plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c)
     : use nat-induction; 3, 12


theorem plus-assoc-r
* \plus(\plus(a)(b))(c) == \plus(a)(\plus(b)(c))

proof
1. \plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c) : use plus-assoc-l;
2. \plus(\plus(a)(b))(c) == \plus(a)(\plus(b)(c)) : use eq-sym; 1
~~~

And $\plus$ is cancellative. This proof is strange because the induction step is trivial.

~~~ {.mycelium}
theorem plus-cancel-r
if
  * \plus(a)(c) == \plus(b)(c)
then
  * a == b

proof
1.    c == \zero : hypothesis c-zero
2.    a : chain
       == \plus(a)(\zero) : flop use plus-zero-r;
       == \plus(a)(c) : flop hypothesis c-zero at z in \plus(a)(z)
       == \plus(b)(c) : assumption 1
       == \plus(b)(\zero) : hypothesis c-zero at z in \plus(b)(z)
       == b : use plus-zero-r;
3.  (c == \zero) => (a == b) : discharge c-zero; 2
4.    (c == n) => (a == b) : hypothesis c-n
5.    (n == n) => (a == b) : sub [c :-> n]; 4
6.    n == n : eq-intro
7.      c == \next(n) : hypothesis c-next
8.      a == b : use impl-elim; 6, 5
9.      (c == \next(n)) /\ (a == b) : use conj-intro; 7, 8
10.     a == b : use conj-elim-r; 9
11.   (c == \next(n)) => (a == b) : discharge c-next; 10
12. ((c == n) => (a == b)) => ((c == \next(n)) => (a == b))
     : discharge c-n; 11
13. ∀k. ((c == k) => (a == b)) => ((c == \next(k)) => (a == b))
     : forall-intro n -> k; 12
14. a == b : use nat-induction; 3, 13


theorem plus-cancel-l
if
  * \plus(c)(a) == \plus(c)(b)
then
  * a == b

proof
1. \plus(a)(c) : chain
    == \plus(c)(a) : use plus-comm;
    == \plus(c)(b) : assumption 1
    == \plus(b)(c) : use plus-comm;
2. a == b : use plus-cancel-r; 1
~~~
