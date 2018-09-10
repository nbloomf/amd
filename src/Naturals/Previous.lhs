---
title: Previous
---

The algebra map $$\either(\only(\zero))(\next) : \Nat \rightarrow \Either\ \Unit\ \Nat$$ is an isomorphism, and in fact we can define its inverse: we'll call this inverse $\prev$.

~~~ {.mycelium}
type \prev :: Nat -> Maybe Nat

definition def-prev
* \prev == \natrec(\nothing)(\opt(\just(\zero))(\comp(\just)(\next)))
~~~

We can compute $\prev$ explicitly on $\zero$:

~~~ {.mycelium}
theorem prev-zero
* \prev(\zero) == \nothing

proof
1. \prev(\zero) : chain
    == \natrec(\nothing)(\opt(\just(\zero))(\comp(\just)(\next)))(\zero)
        : use def-prev; at f in f(\zero)
    == \nothing : use natrec-zero;
~~~

And we can compute $\prev$ on $\next(n)$.

~~~ {.mycelium}
theorem prev-next
* \comp(\prev)(\next) == \just

proof
1.    n == \zero : hypothesis n-zero
2.    \comp(\prev)(\next)(n) : chain
       == \prev(\next(n)) : use def-comp;
       == \prev(\next(\zero)) : hypothesis n-zero at z in \prev(\next(z))
       == \natrec(\nothing)(\opt(\just(\zero))(\comp(\just)(\next)))(\next(\zero))
           : use def-prev; at f in f(\next(\zero))
       == \opt(\just(\zero))(\comp(\just)(\next))(\natrec(\nothing)(\opt(\just(\zero))(\comp(\just)(\next)))(\zero)) : use natrec-next;
       == \opt(\just(\zero))(\comp(\just)(\next))(\nothing) : use natrec-zero; at z in \opt(\just(\zero))(\comp(\just)(\next))(z)
       == \just(\zero) : use opt-nothing;
       == \just(n) : flop hypothesis n-zero at z in \just(z)
3.  (n == \zero) => (\comp(\prev)(\next)(n) == \just(n)) : discharge n-zero; 2
4.    (n == t) => (\comp(\prev)(\next)(n) == \just(n)) : hypothesis n-t
5.    (t == t) => (\comp(\prev)(\next)(t) == \just(t)) : sub [n :-> t]; 4
6.    t == t : eq-intro
7.    \prev(\next(t)) : chain
       == \comp(\prev)(\next)(t) : flop use def-comp;
       == \just(t) : use impl-elim; 6, 5
8.      n == \next(t) : hypothesis n-next
9.      \comp(\prev)(\next)(n) : chain
         == \comp(\prev)(\next)(\next(t)) : hypothesis n-next at z in \comp(\prev)(\next)(z)
         == \prev(\next(\next(t))) : use def-comp;
         == \natrec(\nothing)(\opt(\just(\zero))(\comp(\just)(\next)))(\next(\next(t)))
             : use def-prev; at f in f(\next(\next(t)))
         == \opt(\just(\zero))(\comp(\just)(\next))(\natrec(\nothing)(\opt(\just(\zero))(\comp(\just)(\next)))(\next(t)))
             : use natrec-next;
         == \opt(\just(\zero))(\comp(\just)(\next))(\prev(\next(t)))
             : flop use def-prev; at f in \opt(\just(\zero))(\comp(\just)(\next))(f(\next(t)))
         == \opt(\just(\zero))(\comp(\just)(\next))(\just(t))
             : use reiterate; 7 at z in \opt(\just(\zero))(\comp(\just)(\next))(z)
         == \comp(\just)(\next)(t) : use opt-just;
         == \just(\next(t)) : use def-comp;
         == \just(n) : flop hypothesis n-next at z in \just(z)
10.   (n == \next(t)) => (\comp(\prev)(\next)(n) == \just(n)) : discharge n-next; 9
11. ((n == t) => (\comp(\prev)(\next)(n) == \just(n))) =>
      ((n == \next(t)) => (\comp(\prev)(\next)(n) == \just(n))) : discharge n-t; 10
12. ∀k. ((n == k) => (\comp(\prev)(\next)(n) == \just(n))) =>
      ((n == \next(k)) => (\comp(\prev)(\next)(n) == \just(n))) : forall-intro t -> k; 11
13. \comp(\prev)(\next)(n) == \just(n) : use nat-induction; 3, 12
14. ∀u. \comp(\prev)(\next)(u) == \just(u) : forall-intro n -> u; 13
15. \comp(\prev)(\next) == \just : use fun-eq; 14
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
2. \just(a) : chain
    == \comp(\prev)(\next)(a) : flop use prev-next; at f in f(a)
    == \prev(\next(a)) : use def-comp;
    == \prev(\next(b)) : assumption 1 at z in \prev(z)
    == \comp(\prev)(\next)(b) : flop use def-comp;
    == \just(b) : use prev-next; at f in f(b)
3. a == b : use just-inj; 2
~~~
