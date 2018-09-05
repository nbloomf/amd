---
title: Previous
---

The algebra map $$\either(\only(\zero))(\next) : \Nat \rightarrow \Either\ \Unit\ \Nat$$ is an isomorphism, and in fact we can define its inverse: we'll call this inverse $\prev$.

~~~ {.mycelium}
type \prev :: Nat -> Either Unit Nat

rule def-prev
* \prev == \natrec(\lft(\unit))(\either(\only(\rgt(\zero)))(\comp(\rgt)(\next)))
~~~

We can compute $\prev$ explicitly on $\zero$:

~~~ {.mycelium}
theorem prev-zero
* \prev(\zero) == \lft(\unit)

proof
1. \prev(\zero) : chain
    == \natrec(\lft(\unit))(\either(\only(\rgt(\zero)))(\comp(\rgt)(\next)))(\zero)
        : use def-prev; at f in f(\zero)
    == \lft(\unit) : use natrec-zero;
~~~

And we can compute $\prev$ on $\next(n)$.

~~~ {.mycelium}
theorem prev-next
* \comp(\prev)(\next) == \rgt

proof
1.    n == \zero : hypothesis n-zero
2.    \comp(\prev)(\next)(n) : chain
       == \prev(\next(n)) : use def-comp;
       == \prev(\next(\zero)) : hypothesis n-zero at z in \prev(\next(z))
       == \natrec(\lft(\unit))(\either(\only(\rgt(\zero)))(\comp(\rgt)(\next)))(\next(\zero))
           : use def-prev; at f in f(\next(\zero))
       == \either(\only(\rgt(\zero)))(\comp(\rgt)(\next))(\natrec(\lft(\unit))(\either(\only(\rgt(\zero)))(\comp(\rgt)(\next)))(\zero))
           : use natrec-next;
       == \either(\only(\rgt(\zero)))(\comp(\rgt)(\next))(\lft(\unit))
           : use natrec-zero; at z in \either(\only(\rgt(\zero)))(\comp(\rgt)(\next))(z)
       == \only(\rgt(\zero))(\unit) : use either-lft;
       == \rgt(\zero) : use only-unit;
       == \rgt(n) : flop hypothesis n-zero at z in \rgt(z)
3.  (n == \zero) => (\comp(\prev)(\next)(n) == \rgt(n)) : discharge n-zero; 2
4.    (n == t) => (\comp(\prev)(\next)(n) == \rgt(n)) : hypothesis n-t
5.    (t == t) => (\comp(\prev)(\next)(t) == \rgt(t)) : sub [n :-> t]; 4
6.    t == t : eq-intro
7.    \prev(\next(t)) : chain
       == \comp(\prev)(\next)(t) : flop use def-comp;
       == \rgt(t) : use impl-elim; 6, 5
8.      n == \next(t) : hypothesis n-next
9.      \comp(\prev)(\next)(n) : chain
         == \comp(\prev)(\next)(\next(t)) : hypothesis n-next at z in \comp(\prev)(\next)(z)
         == \prev(\next(\next(t))) : use def-comp;
         == \natrec(\lft(\unit))(\either(\only(\rgt(\zero)))(\comp(\rgt)(\next)))(\next(\next(t)))
             : use def-prev; at f in f(\next(\next(t)))
         == \either(\only(\rgt(\zero)))(\comp(\rgt)(\next))(\natrec(\lft(\unit))(\either(\only(\rgt(\zero)))(\comp(\rgt)(\next)))(\next(t)))
             : use natrec-next;
         == \either(\only(\rgt(\zero)))(\comp(\rgt)(\next))(\prev(\next(t)))
             : flop use def-prev; at f in \either(\only(\rgt(\zero)))(\comp(\rgt)(\next))(f(\next(t)))
         == \either(\only(\rgt(\zero)))(\comp(\rgt)(\next))(\rgt(t))
             : use ap-eq; 7
         == \comp(\rgt)(\next)(t) : use either-rgt;
         == \rgt(\next(t)) : use def-comp;
         == \rgt(n) : flop hypothesis n-next at z in \rgt(z)
10.   (n == \next(t)) => (\comp(\prev)(\next)(n) == \rgt(n)) : discharge n-next; 9
11. ((n == t) => (\comp(\prev)(\next)(n) == \rgt(n))) =>
      ((n == \next(t)) => (\comp(\prev)(\next)(n) == \rgt(n))) : discharge n-t; 10
12. ∀k. ((n == k) => (\comp(\prev)(\next)(n) == \rgt(n))) =>
      ((n == \next(k)) => (\comp(\prev)(\next)(n) == \rgt(n))) : forall-intro t -> k; 11
13. \comp(\prev)(\next)(n) == \rgt(n) : use nat-induction; 3, 12
14. ∀u. \comp(\prev)(\next)(u) == \rgt(u) : forall-intro n -> u; 13
15. \comp(\prev)(\next) == \rgt : use fun-eq; 14
~~~

Using $\prev$ we can show that $\next$ is injective.

~~~ {.mycelium}
theorem next-inj
if
  * \next(a) == \next(b)
then
  * a == b

proof
1. \next(a) == \next(b) : assumption 1
2. \rgt(a) : chain
    == \comp(\prev)(\next)(a) : flop use prev-next; at f in f(a)
    == \prev(\next(a)) : use def-comp;
    == \prev(\next(b)) : assumption 1 at z in \prev(z)
    == \comp(\prev)(\next)(b) : flop use def-comp;
    == \rgt(b) : use prev-next; at f in f(b)
3. a == b : use rgt-inj; 2
~~~
