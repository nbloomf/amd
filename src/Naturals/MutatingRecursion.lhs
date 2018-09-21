---
title: Mutating Recursion
---

Simple recursion bundles a particular recursion scheme into a nicely general package. Let's look at an expanded call tree for an invocation of $\simprec$. Given $\phi$ and $\mu$, and assuming we understand what "3" means, the expression $\simprec(\phi)(\mu)(a)(3)$ expands to

$$\begin{array}{l}
\simprec(\phi)(\mu)(a)(3) = \\
\quad \mu(a,2, \\
\quad\quad \mu(a,1, \\
\quad\quad\quad \mu(a,0, \\
\quad\quad\quad\quad \phi(a))))
\end{array}$$

Note that each time we call $\mu$ with the same $a$ parameter. One way to think about this is that $a$ is a read-only environment we pass to each $\mu$. Together with the $\Nat$ parameter, $\mu$ can do interesting things with $a$, but we can't alter $a$ _inside_ the recursive call -- only outside. This is handier than raw $\natrec$, and still has a nice tail recursive implementation, but there are times when we'd like to alter $a$ both inside and outside the recursive call. We'll introduce such an operator here, called _mutating recursion_.

Specifically, we will show that given constants

$$\left\{\begin{array}{lcl}
 \phi & : & a \rightarrow b \\
 \omega & : & \Nat \rightarrow a \rightarrow a \\
 \mu & : & \Nat \rightarrow a \rightarrow b \rightarrow b
\end{array}\right.$$

there is a unique arrow $\Psi : \Nat \rightarrow a \rightarrow b$ satisfying the following system of equations.

$$\left\{\begin{array}{l}
 \Psi(\zero)(a) = \phi(a) \\
 \Psi(\next(m),a) = \mu(m,a,\Psi(m,\omega(m,a)))
\end{array}\right.$$

Note how $\omega$ and $\mu$ work together to let us do things with $a$ inside the recursive call to $\Psi$ as well as outside.

$$\begin{array}{l}
\mutrec(\phi)(\omega)(\mu)(3)(a) = \\
\quad \mu(2,a, \\
\quad\quad \mu(1,\omega(2,a), \\
\quad\quad\quad \mu(0,\omega(1,\omega(2,a)), \\
\quad\quad\quad\quad \phi(\omega(0,\omega(1,\omega(2,a)))))))
\end{array}$$

The benefit is that $\mutrec$ can succinctly express more interesting functions. One downside is that, as far as I can tell, $\mutrec$ cannot be made tail recursive. Though I'd love to be proven wrong!

By the way, note that $\simprec$ is a special case of $\mutrec$, where $\omega(m) = \id$.

We'll define $\mutrec$ in terms of a helper function, `mutrecH`. Note that $\mutrec$ is defined using $\natrec$, where the natural recursion constructs a function $a \rightarrow \Pair\ \Nat\ b$.

~~~ {.mycelium}
type \mutrecH :: (Nat -> a -> a) -> (Nat -> a -> b -> b) -> (a -> Pair Nat b) -> a -> Pair Nat b

definition def-mutrec-helper
* \mutrecH(omega)(mu)(zeta)(a)
   == \tup(
        \next(\fst(zeta(a))))(
        mu(\fst(zeta(a)))(a)(\snd(zeta(omega(\fst(zeta(a)))(a)))))

type \mutrec :: (a -> b) -> (Nat -> a -> a) -> (Nat -> a -> b -> b) -> Nat -> a -> b

definition def-mutrec
* \mutrec(phi)(omega)(mu)(n)(a)
   == \snd(\natrec(
             \comp(\tup(\zero))(phi))(
             \mutrecH(omega)(mu))(
             n)(
             a))
~~~

Now $\mutrec(\phi)(\omega)(\mu)$ satisfies the first equation:

~~~ {.mycelium}
theorem mutrec-zero
* \mutrec(phi)(omega)(mu)(\zero)(a) == phi(a)

proof
1. \mutrec(phi)(omega)(mu)(\zero)(a) : chain
    == \snd(\natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(
              \zero)(
              a)) : use def-mutrec;
    == \snd(\comp(\tup(\zero))(phi)(a))
     : use natrec-zero; at z in \snd(z(a))
    == \snd(\tup(\zero)(phi(a)))
     : use def-comp; at z in \snd(z)
    == phi(a) : use snd-tup;
~~~

As a special case we can calculate $\mutrec$ on 1.

~~~ {.mycelium}
theorem mutrec-one
* \mutrec(phi)(omega)(mu)(\next(\zero))(a)
   == mu(\zero)(a)(phi(omega(\zero)(a)))

proof
1. \mutrec(phi)(omega)(mu)(\next(\zero))(a) : chain
    == \snd(\natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(
              \next(\zero))(
              a))
     : use def-mutrec;

    == \snd(\mutrecH(omega)(mu)(
         \natrec(
           \comp(\tup(\zero))(phi))(
           \mutrecH(omega)(mu))(
           \zero))(
           a))
     : use natrec-next; at z in \snd(z(a))

    == \snd(\mutrecH(omega)(mu)(\comp(\tup(\zero))(phi))(a))
     : use natrec-zero; at z in
       \snd(\mutrecH(omega)(mu)(z)(a))

    == \snd(\tup(\next(\fst(\comp(\tup(\zero))(phi)(a))))(
         mu(\fst(\comp(\tup(\zero))(phi)(a)))(a)(
           \snd(\comp(\tup(\zero))(phi)(
             omega(\fst(\comp(\tup(\zero))(phi)(a)))(a))))))
     : use def-mutrec-helper; at z in \snd(z)

    == \snd(\tup(\next(\fst(\tup(\zero)(phi(a)))))(
         mu(\fst(\tup(\zero)(phi(a))))(a)(
           \snd(\comp(\tup(\zero))(phi)(
             omega(\fst(\tup(\zero)(phi(a))))(a))))))
     : use def-comp; at z in
       \snd(\tup(\next(\fst(z)))(
         mu(\fst(z))(a)(
           \snd(\comp(\tup(\zero))(phi)(
             omega(\fst(z))(a))))))

    == \snd(\tup(\next(\zero))(
         mu(\zero)(a)(\snd(\comp(\tup(\zero))(phi)(omega(\zero)(a))))))
     : use fst-tup; at z in
       \snd(\tup(\next(z))(
         mu(z)(a)(\snd(\comp(\tup(\zero))(phi)(omega(z)(a))))))

    == mu(\zero)(a)(
         \snd(\comp(\tup(\zero))(phi)(omega(\zero)(a))))
     : use snd-tup;

    == mu(\zero)(a)(\snd(\tup(\zero)(phi(omega(\zero)(a)))))
     : use def-comp; at z in
       mu(\zero)(a)(\snd(z))

    == mu(\zero)(a)(phi(omega(\zero)(a)))
     : use snd-tup; at z in
       mu(\zero)(a)(z)
~~~

Now we can show that $\mutrec$ satisfies the second equation. The bulk of this proof is in a lemma on the inner $\natrec$, on lines 1--13.

~~~ {.mycelium}
theorem mutrec-next
* \mutrec(phi)(omega)(mu)(\next(m))(a)
   == mu(m)(a)(\mutrec(phi)(omega)(mu)(m)(omega(m)(a)))

proof
1.  \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\zero)(a)
      : chain
     == \comp(\tup(\zero))(phi)(a)
      : use natrec-zero; at z in z(a)
     == \tup(\zero)(phi(a))
      : use def-comp;
     == \tup(\zero)(\mutrec(phi)(omega)(mu)(\zero)(a))
      : flop use mutrec-zero; at z in \tup(\zero)(z)

2.    \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a)
       == \tup(n)(\mutrec(phi)(omega)(mu)(n)(a))
        : hypothesis n

3.    \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\next(n))(a)
        : chain

       == \mutrecH(omega)(mu)(\natrec(
            \comp(\tup(\zero))(phi))(
            \mutrecH(omega)(mu))(
            n))(a)
        : use natrec-next; at f in f(a)

       == \tup(\next(\fst(\natrec(
            \comp(\tup(\zero))(phi))(
            \mutrecH(omega)(mu))(n)(a))))(
            mu(\fst(\natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(n)(a)))(a)(\snd(\natrec(
                \comp(\tup(\zero))(phi))(
                \mutrecH(omega)(mu))(n)(omega(\fst(\natrec(
                  \comp(\tup(\zero))(phi))(
                  \mutrecH(omega)(mu))(n)(a)))(a)))))
        : use def-mutrec-helper;

       == \tup(\next(\fst(\tup(n)(
            \mutrec(phi)(omega)(mu)(n)(a)))))(
            mu(\fst(\tup(n)(
              \mutrec(phi)(omega)(mu)(n)(a))))(a)(\snd(
                \natrec(
                  \comp(\tup(\zero))(phi))(
                  \mutrecH(omega)(mu))(n)(
                  omega(\fst(\tup(n)(
                    \mutrec(phi)(omega)(mu)(n)(a))))(a)))))
        : hypothesis n at z in
          \tup(\next(\fst(z)))(
            mu(\fst(z))(a)(\snd(\natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(n)(omega(\fst(z))(a)))))

       == \tup(\next(n))(mu(n)(a)(\snd(\natrec(
            \comp(\tup(\zero))(phi))(
            \mutrecH(omega)(mu))(n)(omega(n)(a)))))
        : use fst-tup; at z in
          \tup(\next(z))(mu(z)(a)(\snd(\natrec(
            \comp(\tup(\zero))(phi))(
            \mutrecH(omega)(mu))(n)(omega(z)(a)))))

       == \tup(\next(n))(mu(\fst(\tup(n)(
            \mutrec(phi)(omega)(mu)(n)(a))))(a)(\snd(\natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(n)(omega(\fst(\tup(n)(
                \mutrec(phi)(omega)(mu)(n)(a))))(a)))))
        : flop use fst-tup; at z in
          \tup(\next(n))(mu(z)(a)(\snd(
            \natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(n)(omega(z)(a)))))

       == \tup(\next(n))(\snd(\tup(\next(\fst(\tup(n)(
            \mutrec(phi)(omega)(mu)(n)(a)))))(
              mu(\fst(\tup(n)(\mutrec(phi)(omega)(mu)(n)(a))))(a)(\snd(
               \natrec(
                 \comp(\tup(\zero))(phi))(
                 \mutrecH(omega)(mu))(n)(
                 omega(\fst(\tup(n)(
                   \mutrec(phi)(omega)(mu)(n)(a))))(a)))))))
        : flop use snd-tup; at z in \tup(\next(n))(z)

       == \tup(\next(n))(\snd(\tup(\next(\fst(
            \natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(n)(a))))(
            mu(\fst(\natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(n)(a)))(a)(\snd(\natrec(
                \comp(\tup(\zero))(phi))(
                \mutrecH(omega)(mu))(n)(
                omega(\fst(\natrec(
                  \comp(\tup(\zero))(phi))(
                  \mutrecH(omega)(mu))(n)(a)))(a)))))))
        : flop hypothesis n at z in
          \tup(\next(n))(\snd(\tup(\next(\fst(z)))(
            mu(\fst(z))(a)(\snd(\natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(n)(omega(\fst(z))(a)))))))

       == \tup(\next(n))(\snd(
            \mutrecH(omega)(mu)(\natrec(
              \comp(\tup(\zero))(phi))(
              \mutrecH(omega)(mu))(n))(a)))
        : flop use def-mutrec-helper; at z in
          \tup(\next(n))(\snd(z))

       == \tup(\next(n))(\snd(\natrec(
            \comp(\tup(\zero))(phi))(
            \mutrecH(omega)(mu))(\next(n))(a)))
        : flop use natrec-next; at z in
          \tup(\next(n))(\snd(z(a)))

       == \tup(\next(n))(\mutrec(phi)(omega)(mu)(\next(n))(a))
        : flop use def-mutrec; at z in
          \tup(\next(n))(z)

4. (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a)
       == \tup(n)(\mutrec(phi)(omega)(mu)(n)(a))) =>
     (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\next(n))(a)
       == \tup(\next(n))(\mutrec(phi)(omega)(mu)(\next(n))(a)))
    : discharge n; 3

5. ∀k. (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(k)(a)
        == \tup(k)(\mutrec(phi)(omega)(mu)(k)(a))) =>
     (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\next(k))(a)
        == \tup(\next(k))(\mutrec(phi)(omega)(mu)(\next(k))(a)))
    : forall-intro n -> k; 4

6. ∀k. (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(k)(a)
        == \tup(k)(\mutrec(phi)(omega)(mu)(k)(a)))
    : invoke nat-induction
      [P :-> (\natrec(
               \comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(_)(a)
              == \tup(_)(\mutrec(phi)(omega)(mu)(_)(a)))]; 1, 5

7. \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a)
    == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a))
     : forall-elim k -> m; 6

8. \mutrec(phi)(omega)(mu)(\next(m))(a) : chain

    == \snd(\natrec(
         \comp(\tup(\zero))(phi))(
         \mutrecH(omega)(mu))(
         \next(m))(
         a))
     : use def-mutrec;

    == \snd(\mutrecH(omega)(mu)(
         \natrec(
           \comp(\tup(\zero))(phi))(
           \mutrecH(omega)(mu))(
           m))(
         a))
     : use natrec-next; at z in \snd(z(a))

    == \snd(\tup(\next(\fst(\natrec(
         \comp(\tup(\zero))(phi))(
         \mutrecH(omega)(mu))(m)(a))))(
           mu(\fst(\natrec(
             \comp(\tup(\zero))(phi))(
             \mutrecH(omega)(mu))(m)(a)))(a)(\snd(\natrec(
               \comp(\tup(\zero))(phi))(
               \mutrecH(omega)(mu))(
               m)(
               omega(\fst(\natrec(
                 \comp(\tup(\zero))(phi))(
                 \mutrecH(omega)(mu))(
                 m)(a)))(a))))))
     : use def-mutrec-helper; at z in \snd(z)

    == mu(\fst(
         \natrec(
           \comp(\tup(\zero))(phi))(
           \mutrecH(omega)(mu))(m)(a)))(
           a)(
           \snd(\natrec(
             \comp(\tup(\zero))(phi))(
             \mutrecH(omega)(mu))(
             m)(
             omega(\fst(\natrec(
               \comp(\tup(\zero))(phi))(
               \mutrecH(omega)(mu))(
               m)(a)))(a))))
     : use snd-tup;

    == mu(\fst(\tup(m)(\mutrec(phi)(omega)(mu)(m)(a))))(a)(
         \snd(\natrec(
           \comp(\tup(\zero))(phi))(
           \mutrecH(omega)(mu))(
           m)(
           omega(\fst(\tup(m)(\mutrec(phi)(omega)(mu)(m)(a))))(a))))
     : use reiterate; 7 at z in
       mu(\fst(z))(a)(
         \snd(\natrec(
           \comp(\tup(\zero))(phi))(
           \mutrecH(omega)(mu))(
           m)(
           omega(\fst(z))(a))))

    == mu(m)(a)(\snd(
         \natrec(
           \comp(\tup(\zero))(phi))(
           \mutrecH(omega)(mu))(
           m)(
           omega(m)(a))))
     : use fst-tup; at z in
       mu(z)(a)(\snd(
         \natrec(
           \comp(\tup(\zero))(phi))(
           \mutrecH(omega)(mu))(
           m)(
           omega(z)(a))))

    == mu(m)(a)(\mutrec(phi)(omega)(mu)(m)(omega(m)(a)))
     : flop use def-mutrec; at z in mu(m)(a)(z)
~~~

Finally, we can use induction to show that $\mutrec(\phi)(\omega)(\mu)$ is unique.

~~~ {.mycelium}
theorem mutrec-unique
if
  * ∀a. t(\zero)(a) == phi(a)
  * ∀a. (∀m. t(\next(m))(a) == mu(m)(a)(t(m)(omega(m)(a))))
then
  * t == \mutrec(phi)(omega)(mu)

proof
1.  ∀u. t(\zero)(u) == phi(u) : assumption 1
2.  t(\zero)(a) == phi(a) : forall-elim u -> a; 1
3.  t(\zero)(a) : chain
     == phi(a) : use reiterate; 2
     == \mutrec(phi)(omega)(mu)(\zero)(a) : flop use mutrec-zero;
4.  ∀u. t(\zero)(u) == \mutrec(phi)(omega)(mu)(\zero)(u)
     : forall-intro a -> u; 3
5.  t(\zero) == \mutrec(phi)(omega)(mu)(\zero)
     : use fun-eq; 4
6.    t(n) == \mutrec(phi)(omega)(mu)(n) : hypothesis n
7.    t(n)(omega(n)(a)) == \mutrec(phi)(omega)(mu)(n)(omega(n)(a))
       : use fun-ap; 6
8.    ∀u. (∀k. t(\next(k))(u) == mu(k)(u)(t(k)(omega(k)(u))))
       : assumption 2
9.    ∀k. t(\next(k))(a) == mu(k)(a)(t(k)(omega(k)(a)))
       : forall-elim u -> a; 8
10.   t(\next(n))(a) == mu(n)(a)(t(n)(omega(n)(a)))
       : forall-elim k -> n; 9
11.   t(\next(n))(a) : chain
       == mu(n)(a)(t(n)(omega(n)(a)))
        : use reiterate; 10
       == mu(n)(a)(\mutrec(phi)(omega)(mu)(n)(omega(n)(a)))
        : use reiterate; 7 at z in mu(n)(a)(z)
       == \mutrec(phi)(omega)(mu)(\next(n))(a)
        : flop use mutrec-next;
12.   ∀u. t(\next(n))(u) == \mutrec(phi)(omega)(mu)(\next(n))(u)
        : forall-intro a -> u; 11
13.   t(\next(n)) == \mutrec(phi)(omega)(mu)(\next(n))
        : use fun-eq; 12
14. (t(n) == \mutrec(phi)(omega)(mu)(n)) =>
      (t(\next(n)) == \mutrec(phi)(omega)(mu)(\next(n)))
     : discharge n; 13
15. ∀u. (t(u) == \mutrec(phi)(omega)(mu)(u)) =>
      (t(\next(u)) == \mutrec(phi)(omega)(mu)(\next(u)))
     : forall-intro n -> u; 14
16. ∀u. t(u) == \mutrec(phi)(omega)(mu)(u)
     : invoke nat-induction
       [P :-> t(_) == \mutrec(phi)(omega)(mu)(_)]; 5, 15
17. t == \mutrec(phi)(omega)(mu) : use fun-eq; 16
~~~

We can also prove that $\simprec$ is a special case of $\mutrec$.

~~~ {.mycelium}
theorem mutrec-simprec
* \flip(\mutrec(phi)(\const(\id))(\flip(mu))) == \simprec(phi)(mu)

proof
1. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(\zero) : chain
    == \mutrec(phi)(\const(\id))(\flip(mu))(\zero)(a) : use def-flip;
    == phi(a) : use mutrec-zero;
2. ∀u. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(u)(\zero) == phi(u)
    : forall-intro a -> u; 1
3. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(\next(m)) : chain
    == \mutrec(phi)(\const(\id))(\flip(mu))(\next(m))(a)
     : use def-flip;
    == \flip(mu)(m)(a)(
         \mutrec(phi)(\const(\id))(\flip(mu))(m)(\const(\id)(m)(a)))
     : use mutrec-next;
    == \flip(mu)(m)(a)(\mutrec(phi)(\const(\id))(\flip(mu))(m)(\id(a)))
     : use def-const; at z in
       \flip(mu)(m)(a)(\mutrec(phi)(\const(\id))(\flip(mu))(m)(z(a)))
    == \flip(mu)(m)(a)(\mutrec(phi)(\const(\id))(\flip(mu))(m)(a))
     : use def-id; at z in
       \flip(mu)(m)(a)(\mutrec(phi)(\const(\id))(\flip(mu))(m)(z))
    == \flip(mu)(m)(a)(\flip(
         \mutrec(phi)(\const(\id))(\flip(mu)))(a)(m))
     : flop use def-flip; at z in
       \flip(mu)(m)(a)(z)
    == mu(a)(m)(\flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(m))
     : use def-flip; at z in
       z(\flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(m))
4. ∀k. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(\next(k))
    == mu(a)(k)(\flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(k))
    : forall-intro m -> k; 3
5. ∀u. (∀k. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(u)(\next(k))
    == mu(u)(k)(\flip(\mutrec(phi)(\const(\id))(\flip(mu)))(u)(k)))
    : forall-intro a -> u; 4
6. \flip(\mutrec(phi)(\const(\id))(\flip(mu))) == \simprec(phi)(mu)
    : use simprec-unique; 2, 5
~~~
