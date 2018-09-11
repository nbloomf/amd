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
* \mutrecH(omega)(mu)(zeta)(a) == \tup(\next(\fst(zeta(a))))(mu(\fst(zeta(a)))(a)(\snd(zeta(omega(\fst(zeta(a)))(a)))))

type \mutrec :: (a -> b) -> (Nat -> a -> a) -> (Nat -> a -> b -> b) -> Nat -> a -> b

definition def-mutrec
* \mutrec(phi)(omega)(mu)(n)(a) == \snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a))
~~~

Now $\mutrec(\phi)(\omega)(\mu)$ satisfies the first equation:

~~~ {.mycelium}
theorem mutrec-zero
* \mutrec(phi)(omega)(mu)(\zero)(a) == phi(a)

proof
1. \mutrec(phi)(omega)(mu)(\zero)(a) : chain
    == \snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\zero)(a)) : use def-mutrec;
    == \snd(\comp(\tup(\zero))(phi)(a)) : use natrec-zero; at z in \snd(z(a))
    == \snd(\tup(\zero)(phi(a))) : use def-comp; at z in \snd(z)
    == phi(a) : use snd-tup;
~~~

As a special case we can calculate $\mutrec$ on 1.

~~~ {.mycelium}
theorem mutrec-one
* \mutrec(phi)(omega)(mu)(\next(\zero))(a) == mu(\zero)(a)(phi(omega(\zero)(a)))

proof
1. \mutrec(phi)(omega)(mu)(\next(\zero))(a) : chain
    == \snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\next(\zero))(a)) : use def-mutrec;
    == \snd(\mutrecH(omega)(mu)(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\zero))(a)) : use natrec-next; at z in \snd(z(a))
    == \snd(\mutrecH(omega)(mu)(\comp(\tup(\zero))(phi))(a)) : use natrec-zero; at z in \snd(\mutrecH(omega)(mu)(z)(a))
    == \snd(\tup(\next(\fst(\comp(\tup(\zero))(phi)(a))))(mu(\fst(\comp(\tup(\zero))(phi)(a)))(a)(\snd(\comp(\tup(\zero))(phi)(omega(\fst(\comp(\tup(\zero))(phi)(a)))(a)))))) : use def-mutrec-helper; at z in \snd(z)
    == \snd(\tup(\next(\fst(\tup(\zero)(phi(a)))))(mu(\fst(\tup(\zero)(phi(a))))(a)(\snd(\comp(\tup(\zero))(phi)(omega(\fst(\tup(\zero)(phi(a))))(a)))))) : use def-comp; at z in \snd(\tup(\next(\fst(z)))(mu(\fst(z))(a)(\snd(\comp(\tup(\zero))(phi)(omega(\fst(z))(a))))))
    == \snd(\tup(\next(\zero))(mu(\zero)(a)(\snd(\comp(\tup(\zero))(phi)(omega(\zero)(a)))))) : use fst-tup; at z in \snd(\tup(\next(z))(mu(z)(a)(\snd(\comp(\tup(\zero))(phi)(omega(z)(a))))))
    == mu(\zero)(a)(\snd(\comp(\tup(\zero))(phi)(omega(\zero)(a)))) : use snd-tup;
    == mu(\zero)(a)(\snd(\tup(\zero)(phi(omega(\zero)(a))))) : use def-comp; at z in mu(\zero)(a)(\snd(z))
    == mu(\zero)(a)(phi(omega(\zero)(a))) : use snd-tup; at z in mu(\zero)(a)(z)
~~~

Now we can show that $\mutrec$ satisfies the second equation. The bulk of this proof is in a lemma on the inner $\natrec$, on lines 1--13.

~~~ {.mycelium}
theorem mutrec-next
* \mutrec(phi)(omega)(mu)(\next(m))(a) == mu(m)(a)(\mutrec(phi)(omega)(mu)(m)(omega(m)(a)))

proof
1.    m == \zero : hypothesis zero
2.    \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) : chain
       == \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\zero)(a) : hypothesis zero at z in \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(z)(a)
       == \comp(\tup(\zero))(phi)(a) : use natrec-zero; at z in z(a)
       == \tup(\zero)(phi(a)) : use def-comp;
       == \tup(m)(phi(a)) : flop hypothesis zero at z in \tup(z)(phi(a))
       == \tup(m)(\mutrec(phi)(omega)(mu)(\zero)(a)) : flop use mutrec-zero; at z in \tup(m)(z)
       == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a)) : flop hypothesis zero at z in \tup(m)(\mutrec(phi)(omega)(mu)(z)(a))
3.  (m == \zero) => (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a))) : discharge zero; 2
4.    (m == n) => (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a))) : hypothesis n
5.    (n == n) => (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a) == \tup(n)(\mutrec(phi)(omega)(mu)(n)(a))) : sub [m :-> n]; 4
6.    n == n : eq-intro
7.    \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a) == \tup(n)(\mutrec(phi)(omega)(mu)(n)(a)) : use impl-elim; 6, 5
8.      m == \next(n) : hypothesis next
9.      \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) : chain
         == \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\next(n))(a) : hypothesis next at z in \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(z)(a)
         == \mutrecH(omega)(mu)(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n))(a) : use natrec-next; at f in f(a)
         == \tup(\next(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a))))(mu(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a)))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a)))(a))))) : use def-mutrec-helper;
         == \tup(\next(\fst(\tup(n)(\mutrec(phi)(omega)(mu)(n)(a)))))(mu(\fst(\tup(n)(\mutrec(phi)(omega)(mu)(n)(a))))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(\fst(\tup(n)(\mutrec(phi)(omega)(mu)(n)(a))))(a))))) : use reiterate; 7 at z in \tup(\next(\fst(z)))(mu(\fst(z))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(\fst(z))(a)))))
         == \tup(\next(n))(mu(n)(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(n)(a))))) : use fst-tup; at z in \tup(\next(z))(mu(z)(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(z)(a)))))
         == \tup(\next(n))(mu(\fst(\tup(n)(\mutrec(phi)(omega)(mu)(n)(a))))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(\fst(\tup(n)(\mutrec(phi)(omega)(mu)(n)(a))))(a))))) : flop use fst-tup; at z in \tup(\next(n))(mu(z)(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(z)(a)))))
         == \tup(\next(n))(\snd(\tup(\next(\fst(\tup(n)(\mutrec(phi)(omega)(mu)(n)(a)))))(mu(\fst(\tup(n)(\mutrec(phi)(omega)(mu)(n)(a))))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(\fst(\tup(n)(\mutrec(phi)(omega)(mu)(n)(a))))(a))))))) : flop use snd-tup; at z in \tup(\next(n))(z)
         == \tup(\next(n))(\snd(\tup(\next(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a))))(mu(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a)))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(a)))(a))))))) : flop use reiterate; 7 at z in \tup(\next(n))(\snd(\tup(\next(\fst(z)))(mu(\fst(z))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n)(omega(\fst(z))(a)))))))
         == \tup(\next(n))(\snd(\mutrecH(omega)(mu)(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(n))(a))) : flop use def-mutrec-helper; at z in \tup(\next(n))(\snd(z))
         == \tup(\next(n))(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\next(n))(a))) : flop use natrec-next; at z in \tup(\next(n))(\snd(z(a)))
         == \tup(\next(n))(\mutrec(phi)(omega)(mu)(\next(n))(a)) : flop use def-mutrec; at z in \tup(\next(n))(z)
         == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a)) : flop hypothesis next at z in \tup(z)(\mutrec(phi)(omega)(mu)(z)(a))
10.   (m == \next(n)) => (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a))) : discharge next; 9
11. ((m == n) => (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a)))) =>
      ((m == \next(n)) => (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a)))) : discharge n; 10
12. ∀k. ((m == k) => (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a)))) =>
      ((m == \next(k)) => (\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a)))) : forall-intro n -> k; 11
13. \natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a) == \tup(m)(\mutrec(phi)(omega)(mu)(m)(a)) : use nat-induction; 3, 12
14. \mutrec(phi)(omega)(mu)(\next(m))(a) : chain
     == \snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(\next(m))(a)) : use def-mutrec;
     == \snd(\mutrecH(omega)(mu)(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m))(a)) : use natrec-next; at z in \snd(z(a))
     == \snd(\tup(\next(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a))))(mu(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a)))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(omega(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a)))(a)))))) : use def-mutrec-helper; at z in \snd(z)
     == mu(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a)))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(omega(\fst(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(a)))(a)))) : use snd-tup;
     == mu(\fst(\tup(m)(\mutrec(phi)(omega)(mu)(m)(a))))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(omega(\fst(\tup(m)(\mutrec(phi)(omega)(mu)(m)(a))))(a)))) : use reiterate; 13 at z in mu(\fst(z))(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(omega(\fst(z))(a))))
     == mu(m)(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(omega(m)(a)))) : use fst-tup; at z in mu(z)(a)(\snd(\natrec(\comp(\tup(\zero))(phi))(\mutrecH(omega)(mu))(m)(omega(z)(a))))
     == mu(m)(a)(\mutrec(phi)(omega)(mu)(m)(omega(m)(a))) : flop use def-mutrec; at z in mu(m)(a)(z)
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
1.    m == \zero : hypothesis zero
2.    ∀u. t(\zero)(u) == phi(u) : assumption 1
3.    t(\zero)(a) == phi(a) : forall-elim u -> a; 2
4.    t(m)(a) : chain
       == t(\zero)(a) : hypothesis zero at z in t(z)(a)
       == phi(a) : use reiterate; 3
       == \mutrec(phi)(omega)(mu)(\zero)(a) : flop use mutrec-zero;
       == \mutrec(phi)(omega)(mu)(m)(a) : flop hypothesis zero at z in \mutrec(phi)(omega)(mu)(z)(a)
5.  (m == \zero) => (t(m)(a) == \mutrec(phi)(omega)(mu)(m)(a)) : discharge zero; 4
6.    (m == n) => (t(m)(a) == \mutrec(phi)(omega)(mu)(m)(a)) : hypothesis n
7.    (n == n) => (t(n)(omega(n)(a)) == \mutrec(phi)(omega)(mu)(n)(omega(n)(a))) : sub [m :-> n; a :-> omega(n)(a)]; 6
8.    n == n : eq-intro
9.    t(n)(omega(n)(a)) == \mutrec(phi)(omega)(mu)(n)(omega(n)(a)) : use impl-elim; 8, 7
10.   ∀u. (∀k. t(\next(k))(u) == mu(k)(u)(t(k)(omega(k)(u)))) : assumption 2
11.   ∀k. t(\next(k))(a) == mu(k)(a)(t(k)(omega(k)(a))) : forall-elim u -> a; 10
12.   t(\next(n))(a) == mu(n)(a)(t(n)(omega(n)(a))) : forall-elim k -> n; 11
13.     m == \next(n) : hypothesis next
14.     t(m)(a) : chain
         == t(\next(n))(a) : hypothesis next at z in t(z)(a)
         == mu(n)(a)(t(n)(omega(n)(a))) : use reiterate; 12
         == mu(n)(a)(\mutrec(phi)(omega)(mu)(n)(omega(n)(a))) : use reiterate; 9 at z in mu(n)(a)(z)
         == \mutrec(phi)(omega)(mu)(\next(n))(a) : flop use mutrec-next;
         == \mutrec(phi)(omega)(mu)(m)(a) : flop hypothesis next at z in \mutrec(phi)(omega)(mu)(z)(a)
15.   (m == \next(n)) => (t(m)(a) == \mutrec(phi)(omega)(mu)(m)(a)) : discharge next; 14
16. ((m == n) => (t(m)(a) == \mutrec(phi)(omega)(mu)(m)(a))) =>
      ((m == \next(n)) => (t(m)(a) == \mutrec(phi)(omega)(mu)(m)(a))) : discharge n; 15
17. ∀k. ((m == k) => (t(m)(a) == \mutrec(phi)(omega)(mu)(m)(a))) =>
      ((m == \next(k)) => (t(m)(a) == \mutrec(phi)(omega)(mu)(m)(a))) : forall-intro n -> k; 16
18. t(m)(a) == \mutrec(phi)(omega)(mu)(m)(a) : use nat-induction; 5, 17
19. ∀u. t(m)(u) == \mutrec(phi)(omega)(mu)(m)(u) : forall-intro a -> u; 18
20. t(m) == \mutrec(phi)(omega)(mu)(m) : use fun-eq; 19
21. ∀u. t(u) == \mutrec(phi)(omega)(mu)(u) : forall-intro m -> u; 20
22. t == \mutrec(phi)(omega)(mu) : use fun-eq; 21
~~~

We can also prove that $\simprec$ is a special case of $\mutrec$.

~~~ {.mycelium}
theorem mutrec-simprec
* \flip(\mutrec(phi)(\const(\id))(\flip(mu))) == \simprec(phi)(mu)

proof
1. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(\zero) : chain
    == \mutrec(phi)(\const(\id))(\flip(mu))(\zero)(a) : use def-flip;
    == phi(a) : use mutrec-zero;
2. ∀u. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(u)(\zero) == phi(u) : forall-intro a -> u; 1
3. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(\next(m)) : chain
    == \mutrec(phi)(\const(\id))(\flip(mu))(\next(m))(a) : use def-flip;
    == \flip(mu)(m)(a)(\mutrec(phi)(\const(\id))(\flip(mu))(m)(\const(\id)(m)(a))) : use mutrec-next;
    == \flip(mu)(m)(a)(\mutrec(phi)(\const(\id))(\flip(mu))(m)(\id(a))) : use def-const; at z in \flip(mu)(m)(a)(\mutrec(phi)(\const(\id))(\flip(mu))(m)(z(a)))
    == \flip(mu)(m)(a)(\mutrec(phi)(\const(\id))(\flip(mu))(m)(a)) : use def-id; at z in \flip(mu)(m)(a)(\mutrec(phi)(\const(\id))(\flip(mu))(m)(z))
    == \flip(mu)(m)(a)(\flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(m)) : flop use def-flip; at z in \flip(mu)(m)(a)(z)
    == mu(a)(m)(\flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(m)) : use def-flip; at z in z(\flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(m))
4. ∀k. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(\next(k)) == mu(a)(k)(\flip(\mutrec(phi)(\const(\id))(\flip(mu)))(a)(k)) : forall-intro m -> k; 3
5. ∀u. (∀k. \flip(\mutrec(phi)(\const(\id))(\flip(mu)))(u)(\next(k)) == mu(u)(k)(\flip(\mutrec(phi)(\const(\id))(\flip(mu)))(u)(k))) : forall-intro a -> u; 4
6. \flip(\mutrec(phi)(\const(\id))(\flip(mu))) == \simprec(phi)(mu) : use simprec-unique; 2, 5
~~~