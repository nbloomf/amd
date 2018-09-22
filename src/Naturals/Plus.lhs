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
1. \plus(\next(a))(\zero) : chain
    == \next(a) : use plus-zero-r;
    == \next(\plus(a)(\zero))
     : flop use plus-zero-r; at z in \next(z)

2.   \plus(\next(a))(n) == \next(\plus(a)(n)) : hypothesis n

3.   \plus(\next(a))(\next(n)) : chain
      == \next(\plus(\next(a))(n)) : use plus-next-r;
      == \next(\next(\plus(a)(n))) : use ap-eq; 2
      == \next(\plus(a)(\next(n)))
       : flop use plus-next-r; at z in \next(z)

4. (\plus(\next(a))(n) == \next(\plus(a)(n))) =>
     (\plus(\next(a))(\next(n)) == \next(\plus(a)(\next(n))))
   : discharge n; 3

5. ∀k. (\plus(\next(a))(k) == \next(\plus(a)(k))) =>
     (\plus(\next(a))(\next(k)) == \next(\plus(a)(\next(k))))
   : forall-intro n -> k; 4

6. ∀k. \plus(\next(a))(k) == \next(\plus(a)(k))
   : invoke nat-induction
     [P :-> \plus(\next(a))(_) == \next(\plus(a)(_))]; 1, 5

7. \plus(\next(a))(b) == \next(\plus(a)(b))
   : forall-elim k -> b; 6
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
1. \plus(\zero)(b) : chain
    == b : use plus-zero-l;
    == \plus(b)(\zero) : flop use plus-zero-r;

2.   \plus(n)(b) == \plus(b)(n) : hypothesis n

3.   \plus(\next(n))(b) : chain
      == \next(\plus(n)(b)) : use plus-next-l;
      == \next(\plus(b)(n)) : use ap-eq; 2
      == \plus(b)(\next(n)) : flop use plus-next-r;

4. (\plus(n)(b) == \plus(b)(n)) =>
     (\plus(\next(n))(b) == \plus(b)(\next(n)))
    : discharge n; 3

5. ∀k. (\plus(k)(b) == \plus(b)(k)) =>
     (\plus(\next(k))(b) == \plus(b)(\next(k)))
    : forall-intro n -> k; 4

6. ∀k. \plus(k)(b) == \plus(b)(k)
    : invoke nat-induction
      [P :-> \plus(_)(b) == \plus(b)(_)]; 1, 5

7. \plus(a)(b) == \plus(b)(a)
    : forall-elim k -> a; 6
~~~

$\plus$ is associative.

~~~ {.mycelium}
theorem plus-assoc-l
* \plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c)

proof
1. \plus(a)(\plus(b)(\zero)) : chain
    == \plus(a)(b) : use plus-zero-r; at z in \plus(a)(z)
    == \plus(\plus(a)(b))(\zero) : flop use plus-zero-r;

2.   \plus(a)(\plus(b)(n)) == \plus(\plus(a)(b))(n) : hypothesis n

3.   \plus(a)(\plus(b)(\next(n))) : chain
      == \plus(a)(\next(\plus(b)(n)))
       : use plus-next-r; at z in \plus(a)(z)
      == \next(\plus(a)(\plus(b)(n)))
       : use plus-next-r;
      == \next(\plus(\plus(a)(b))(n))
       : use ap-eq; 2
      == \plus(\plus(a)(b))(\next(n))
       : flop use plus-next-r;

4. (\plus(a)(\plus(b)(n)) == \plus(\plus(a)(b))(n)) =>
     (\plus(a)(\plus(b)(\next(n))) == \plus(\plus(a)(b))(\next(n)))
    : discharge n; 3

5. ∀k. (\plus(a)(\plus(b)(k)) == \plus(\plus(a)(b))(k)) =>
     (\plus(a)(\plus(b)(\next(k))) == \plus(\plus(a)(b))(\next(k)))
    : forall-intro n -> k; 4

6. ∀k. \plus(a)(\plus(b)(k)) == \plus(\plus(a)(b))(k)
    : invoke nat-induction
      [P :-> \plus(a)(\plus(b)(_)) == \plus(\plus(a)(b))(_)]; 1, 5

7. \plus(a)(\plus(b)(c)) == \plus(\plus(a)(b))(c)
    : forall-elim k -> c; 6


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
1.    \plus(a)(\zero) == \plus(b)(\zero)
       : hypothesis zero

2.    a : chain
       == \plus(a)(\zero) : flop use plus-zero-r;
       == \plus(b)(\zero) : hypothesis zero
       == b : use plus-zero-r;

3.  (\plus(a)(\zero) == \plus(b)(\zero)) =>
      (a == b) : discharge zero; 2

4.    (\plus(a)(n) == \plus(b)(n)) => (a == b)
       : hypothesis n

5.      \plus(a)(\next(n)) == \plus(b)(\next(n))
         : hypothesis next

6.      \next(\plus(a)(n)) : chain
         == \plus(a)(\next(n)) : flop use plus-next-r;
         == \plus(b)(\next(n)) : hypothesis next
         == \next(\plus(b)(n)) : use plus-next-r;

7.      \plus(a)(n) == \plus(b)(n) : use next-inj; 6

8.      a == b : use impl-elim; 7, 4

9.    (\plus(a)(\next(n)) == \plus(b)(\next(n))) => (a == b)
       : discharge next; 8

10. ((\plus(a)(n) == \plus(b)(n)) => (a == b)) =>
      ((\plus(a)(\next(n)) == \plus(b)(\next(n))) => (a == b))
     : discharge n; 9

11. ∀k. ((\plus(a)(k) == \plus(b)(k)) => (a == b)) =>
      ((\plus(a)(\next(k)) == \plus(b)(\next(k))) => (a == b))
     : forall-intro n -> k; 10

12. ∀k. (\plus(a)(k) == \plus(b)(k)) => (a == b)
     : invoke nat-induction
       [P :-> (\plus(a)(_) == \plus(b)(_)) => (a == b)]; 3, 11

13. (\plus(a)(c) == \plus(b)(c)) => (a == b)
     : forall-elim k -> c; 12

14. \plus(a)(c) == \plus(b)(c)
     : assumption 1

15. a == b : use impl-elim; 14, 13


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

~~~ {.mycelium}
theorem plus-self-cancel-l
if
  * a == \plus(a)(b)
then
  * b == \zero

proof
1. \plus(a)(b) : chain
    == a
     : flop assumption 1
    == \plus(a)(\zero)
     : flop use plus-zero-r;

2. b == \zero : use plus-cancel-l; 1


theorem plus-self-cancel-r
if
  * a == \plus(b)(a)
then
  * b == \zero

proof
1. a : chain
    == \plus(b)(a) : assumption 1
    == \plus(a)(b) : use plus-comm;

2. b == \zero : use plus-self-cancel-l; 1
~~~
