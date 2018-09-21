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
1. \comp(\prev)(\next)(\zero) : chain

    == \prev(\next(\zero))
     : use def-comp;

    == \natrec(
         \nothing)(
         \opt(\just(\zero))(\comp(\just)(\next)))(
         \next(\zero))
     : use def-prev; at f in
       f(\next(\zero))

    == \opt(
         \just(\zero))(
         \comp(\just)(\next))(
           \natrec(
             \nothing)(
             \opt(\just(\zero))(\comp(\just)(\next)))(
             \zero))
     : use natrec-next;

    == \opt(\just(\zero))(\comp(\just)(\next))(\nothing)
     : use natrec-zero; at z in
       \opt(\just(\zero))(\comp(\just)(\next))(z)

    == \just(\zero) : use opt-nothing;

2.   \comp(\prev)(\next)(n) == \just(n) : hypothesis n

3.   \comp(\prev)(\next)(\next(n)) : chain

      == \prev(\next(\next(n))) : use def-comp;

      == \natrec(
           \nothing)(
           \opt(\just(\zero))(\comp(\just)(\next)))(
           \next(\next(n)))
       : use def-prev; at f in
         f(\next(\next(n)))

      == \opt(\just(\zero))(\comp(\just)(\next))(
           \natrec(
             \nothing)(
             \opt(\just(\zero))(\comp(\just)(\next)))(
             \next(n)))
       : use natrec-next;

      == \opt(\just(\zero))(\comp(\just)(\next))(\prev(\next(n)))
       : flop use def-prev; at f in
         \opt(\just(\zero))(\comp(\just)(\next))(f(\next(n)))

      == \opt(\just(\zero))(\comp(\just)(\next))(\comp(\prev)(\next)(n))
       : flop use def-comp; at z in
         \opt(\just(\zero))(\comp(\just)(\next))(z)

      == \opt(\just(\zero))(\comp(\just)(\next))(\just(n))
       : hypothesis n at z in
         \opt(\just(\zero))(\comp(\just)(\next))(z)

      == \comp(\just)(\next)(n) : use opt-just;

      == \just(\next(n)) : use def-comp;

4. (\comp(\prev)(\next)(n) == \just(n)) =>
     (\comp(\prev)(\next)(\next(n)) == \just(\next(n)))
   : discharge n; 3

5. ∀k. (\comp(\prev)(\next)(k)
        == \just(k)) =>
     (\comp(\prev)(\next)(\next(k))
        == \just(\next(k)))
   : forall-intro n -> k; 4

6. ∀k. \comp(\prev)(\next)(k) == \just(k)
   : invoke nat-induction
     [P :-> \comp(\prev)(\next)(_) == \just(_)]; 1, 5

7. \comp(\prev)(\next) == \just
   : use fun-eq; 6
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
