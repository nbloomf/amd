---
title: Simple Recursion
---

$\natrec$ is the standard way to define a recursive function on $\Nat$, but in some practical cases using raw $\natrec$ is awkward. For example the signature of a function defined with $\natrec$ will always be $$\Nat \rightarrow a$$ for some type $a$, but some recursive functions are more naturally thought of as having more detailed signatures. We can achieve this by replacing $a$ with something more complicated, but the definitions in terms of $\natrec$ will tend to get confusing quickly. In a concrete sense, $\natrec$ is too powerful; too low-level.

This is analogous to the problem with `goto` in imperative languages. It allows for arbitrary control flow, but in many cases we don't really want _arbitrary_ control flow; we want control flow following one of a few simple patterns.

The solution to both of these problems is to introduce higher-level constructs with simpler semantics. Instead of `goto`, we use e.g. `if`, `for`, `while`, and `throw/catch`. And rather than raw $\natrec$, we'll use higher level _recursion operators_. In this post we introduce the first of these: simple recursion with a parameter, denoted $\simprec$.

Given constants

$$\left\{\begin{array}{lcl}
\phi & : & a \rightarrow b \\
\mu & : & a \rightarrow \Nat \rightarrow b \rightarrow b,
\end{array}\right.$$

$\simprec(\phi)(\mu)$ is the unique function $\Psi : a \rightarrow \Nat \rightarrow b$ satisfying the following system of equations.

$$\left\{\begin{array}{l}
\Psi(a,\zero) = \phi(a) \\
\Psi(a,\next(n)) = \mu(a,n,\Psi(a,n))
\end{array}\right.$$

We could think of this system like a "definition" for $\Psi$, since in principle it gives a recursive strategy for evaluating $\Psi(a,n)$ for any $a$ and $n$. But as definitions go it's hard to use this to answer important questions. Does this $\Psi$ terminate? Why should $\Psi$ be unique? For that matter does $\Psi$ really exist? What does it even mean to say that a function exists when it is defined recursively like this?

So instead of using this system of equations as a definition, we'll define $\simprec$ in terms of $\natrec$ and prove that it is the unique solution to the system. The equations can be thought of as a _universal property_ satisfied by $\simprec$, rather than as a definition of $\simprec$ -- and this is vastly more powerful. Taking some liberties with notation, the existence and uniqueness of $\Psi$ as a solution to that system of equations is equivalent to the uniqueness of $\Psi$ making the following diagrams commute.

$$\require{AMScd}
\begin{CD}
(a,\Unit) @>{(\id,\zero)}>> (a,\Nat) \\
@V{\phi}VV @VV{\Psi}V \\
b @= b
\end{CD}
\quad\quad
\begin{CD}
(a,\Nat) @>{(\id,\next)}>> (a,\Nat) \\
@V{(\id,\Psi)}VV @VV{\Psi}V \\
(a,\Nat,b) @>>{\mu}> b
\end{CD}$$

The definition of $\simprec$ is a little long but we only have to deal with it directly while establishing the universal property. The universal property acts like a contract on the behavior of $\simprec$; any other property $\simprec$ enjoys can be proved in terms of the contract, rather than in terms of the definition.

This is also where having our proofs mechanically checked really shines. The details of the proofs in this section are long and tedious, but they can be safely ignored if we trust the proof checker.

Here's the signature and definition of $\simprec$.

~~~ {.mycelium}
type \simprec :: (a -> b) -> (a -> Nat -> b -> b) -> a -> Nat -> b

definition def-simprec
* \simprec(phi)(mu)(a)(n)
   == \snd(
        \natrec(
          \tup(\zero)(phi(a)))(
          \pair(\comp(\next)(\fst))(
          \uncurry(mu(a))))(
          n))
~~~

At this point you might reasonably ask -- _where the heck did that come from?_ And that is a very, very good question. We'll get to that later.

First we'll show that $\simprec$ satisfies the first equation in the UP. This part is easy.

~~~ {.mycelium}
theorem simprec-zero
* \simprec(phi)(mu)(a)(\zero) == phi(a)

proof
1. \simprec(phi)(mu)(a)(\zero) : chain
    == \snd(
         \natrec(
           \tup(\zero)(phi(a)))(
           \pair(\comp(\next)(\fst))(
           \uncurry(mu(a))))(
           \zero))
        : use def-simprec;
    == \snd(\tup(\zero)(phi(a)))
        : use natrec-zero; at z in \snd(z)
    == phi(a) : use snd-tup;
~~~

Next we show that $\simprec$ satisfies the second equation in the UP. This part is... less easy.

This proof looks really complicated, but it can be broken down to a simple structure. Lines 1--7 prove a lemma using natural number induction, showing that

$$\begin{array}{l}
\natrec(\tup(\zero)(\phi(a)))(\pair(\comp(\next)(\fst))(\uncurry(\mu(a))))(m) \\
\quad = \tup(m)(\simprec(\phi)(\mu)(a)(m)).
\end{array}$$

(Why? Because that's what we need.) From there we show the main result, again using natural number induction.

~~~ {.mycelium}
theorem simprec-next
* \simprec(phi)(mu)(a)(\next(m)) == mu(a)(m)(\simprec(phi)(mu)(a)(m))

proof
1.  \natrec(
      \tup(\zero)(phi(a)))(
      \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
      \zero)
      : chain

     == \tup(\zero)(phi(a))
      : use natrec-zero;

     == \tup(\zero)(\simprec(phi)(mu)(a)(\zero))
      : flop use simprec-zero; at z in
          \tup(\zero)(z)

2.    \natrec(
        \tup(\zero)(phi(a)))(
        \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
        n)

       == \tup(n)(\simprec(phi)(mu)(a)(n))
        : hypothesis l-next

3.    \natrec(
        \tup(\zero)(phi(a)))(
        \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
        \next(n))
        : chain

       == \pair(\comp(\next)(\fst))(\uncurry(mu(a)))(
            \natrec(
              \tup(\zero)(phi(a)))(
              \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
              n))
        : use natrec-next;

       == \pair(\comp(\next)(\fst))(\uncurry(mu(a)))(
            \tup(n)(\simprec(phi)(mu)(a)(n)))
        : hypothesis l-next at z in
          \pair(\comp(\next)(\fst))(\uncurry(mu(a)))(z)

       == \tup(
            \comp(\next)(\fst)(\tup(n)(\simprec(phi)(mu)(a)(n))))(
            \uncurry(mu(a))(\tup(n)(\simprec(phi)(mu)(a)(n))))
        : flop use pair-tup;

       == \tup(
            \next(\fst(\tup(n)(\simprec(phi)(mu)(a)(n)))))(
            \uncurry(mu(a))(\tup(n)(\simprec(phi)(mu)(a)(n))))
        : use def-comp; at z in
          \tup(z)(\uncurry(mu(a))(\tup(n)(\simprec(phi)(mu)(a)(n))))

       == \tup(
            \next(n))(
            \uncurry(mu(a))(\tup(n)(\simprec(phi)(mu)(a)(n))))
        : use fst-tup; at z in
          \tup(
            \next(z))(
            \uncurry(mu(a))(\tup(n)(\simprec(phi)(mu)(a)(n))))

       == \tup(
            \next(n))(
            mu(a)(n)(\simprec(phi)(mu)(a)(n)))
        : use uncurry-tup; at z in
          \tup(\next(n))(z)

       == \tup(
            \next(n))(
            mu(a)(n)(\snd(\tup(n)(\simprec(phi)(mu)(a)(n)))))
        : flop use snd-tup; at z in
          \tup(\next(n))(mu(a)(n)(z))

       == \tup(
            \next(n))(
            mu(a)(
              n)(
              \snd(\natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                n))))
        : flop hypothesis l-next at z in
          \tup(\next(n))(mu(a)(n)(\snd(z)))

       == \tup(
            \next(n))(
            mu(a)(
              \fst(\tup(n)(\simprec(phi)(mu)(a)(n))))(
              \snd(\natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                n))))
        : flop use fst-tup; at z in
          \tup(
            \next(n))(
            mu(a)(
              z)(
              \snd(\natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                n))))

       == \tup(
            \next(n))(
            mu(a)(
              \fst(\natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                n)))(
              \snd(\natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                n))))
        : flop hypothesis l-next at z in
          \tup(
            \next(n))(
            mu(a)(
              \fst(z))(
              \snd(\natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                n))))

       == \tup(
            \next(n))(
            \uncurry(mu(a))(
              \natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                n)))
        : flop use def-uncurry; at z in
          \tup(\next(n))(z)

       == \tup(
            \next(n))(
            \snd(
              \pair(\comp(\next)(\fst))(\uncurry(mu(a)))(
              \natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                n))))
        : flop use snd-pair; at z in
          \tup(\next(n))(z)

       == \tup(
            \next(n))(
            \snd(
              \natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(
                \uncurry(mu(a))))(
              \next(n))))
        : flop use natrec-next; at z in
          \tup(\next(n))(\snd(z))

       == \tup(
            \next(n))(
            \simprec(phi)(mu)(a)(\next(n)))
        : flop use def-simprec; at z in
          \tup(\next(n))(z)

4.  (\natrec(
      \tup(\zero)(phi(a)))(
      \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
      n)
     == \tup(n)(\simprec(phi)(mu)(a)(n))) =>
    (\natrec(
      \tup(\zero)(phi(a)))(
      \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
      \next(n))
     == \tup(\next(n))(\simprec(phi)(mu)(a)(\next(n))))
      : discharge l-next; 3

5.  ∀k. (\natrec(
          \tup(\zero)(phi(a)))(
          \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
          k) == \tup(k)(\simprec(phi)(mu)(a)(k))) =>
      (\natrec(
        \tup(\zero)(phi(a)))(
        \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
        \next(k))
       == \tup(\next(k))(\simprec(phi)(mu)(a)(\next(k))))
     : forall-intro n -> k; 4

6.  ∀n. \natrec(
         \tup(\zero)(phi(a)))(
         \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
         n) == \tup(n)(\simprec(phi)(mu)(a)(n))
     : invoke nat-induction
       [ P :-> \natrec(
                 \tup(\zero)(phi(a)))(
                 \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                 _)
                == \tup(_)(\simprec(phi)(mu)(a)(_)) ]; 1, 5

7.  \natrec(
      \tup(\zero)(phi(a)))(
      \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
      m)
     == \tup(m)(\simprec(phi)(mu)(a)(m))
      : forall-elim n -> m; 6

8.    m == \zero : hypothesis zero

9.    \simprec(phi)(mu)(a)(\next(m)) : chain

       == \simprec(phi)(mu)(a)(\next(\zero))
        : hypothesis zero at z in
          \simprec(phi)(mu)(a)(\next(z))

       == \snd(\natrec(
            \tup(\zero)(phi(a)))(
            \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
            \next(\zero)))
        : use def-simprec;

       == \snd(\pair(\comp(\next)(\fst))(\uncurry(mu(a)))(
            \natrec(
              \tup(\zero)(phi(a)))(
              \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
              \zero)))
        : use natrec-next; at z in \snd(z)

       == \snd(\pair(\comp(\next)(\fst))(\uncurry(mu(a)))(
            \tup(\zero)(phi(a))))
        : use natrec-zero; at z in
          \snd(\pair(\comp(\next)(\fst))(\uncurry(mu(a)))(z))

       == \uncurry(mu(a))(\tup(\zero)(phi(a)))
        : use snd-pair;

       == mu(a)(\zero)(phi(a))
        : use uncurry-tup;

       == mu(a)(\zero)(\simprec(phi)(mu)(a)(\zero))
        : flop use simprec-zero; at z in
          mu(a)(\zero)(z)

       == mu(a)(m)(\simprec(phi)(mu)(a)(m))
        : flop hypothesis zero at z in
          mu(a)(z)(\simprec(phi)(mu)(a)(z))

10. (m == \zero) =>
      (\simprec(phi)(mu)(a)(\next(m))
        == mu(a)(m)(\simprec(phi)(mu)(a)(m)))
     : discharge zero; 9

11.   ∃k. m == \next(k) : hypothesis ex

12.     m == \next(t) : hypothesis t

13.     \simprec(phi)(mu)(a)(\next(m)) : chain

         == \simprec(phi)(mu)(a)(\next(\next(t)))
          : hypothesis t at z in
            \simprec(phi)(mu)(a)(\next(z))

         == \snd(\natrec(
              \tup(\zero)(phi(a)))(
              \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
              \next(\next(t))))
          : use def-simprec;

         == \snd(\pair(\comp(\next)(\fst))(\uncurry(mu(a)))(
              \natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                \next(t))))
          : use natrec-next; at z in
            \snd(z)

         == \uncurry(mu(a))(
              \natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                \next(t)))
          : use snd-pair;

         == \uncurry(mu(a))(
              \natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                m))
          : flop hypothesis t at z in
            \uncurry(mu(a))(
              \natrec(
                \tup(\zero)(phi(a)))(
                \pair(\comp(\next)(\fst))(\uncurry(mu(a))))(
                z))

         == \uncurry(mu(a))(\tup(m)(\simprec(phi)(mu)(a)(m)))
          : use reiterate; 7 at z in
            \uncurry(mu(a))(z)

         == mu(a)(m)(\simprec(phi)(mu)(a)(m))
          : use uncurry-tup;

14.   (m == \next(t)) =>
        (\simprec(phi)(mu)(a)(\next(m))
          == mu(a)(m)(\simprec(phi)(mu)(a)(m)))
       : discharge t; 13

15.   \simprec(phi)(mu)(a)(\next(m))
       == mu(a)(m)(\simprec(phi)(mu)(a)(m))
        : exists-elim t <- k; 11, 14

16. (∃k. m == \next(k)) =>
      (\simprec(phi)(mu)(a)(\next(m))
        == mu(a)(m)(\simprec(phi)(mu)(a)(m)))
      : discharge ex; 15

17. \simprec(phi)(mu)(a)(\next(m))
     == mu(a)(m)(\simprec(phi)(mu)(a)(m))
      : use nat-cases-1; 10, 16
~~~

Finally, we show that $\simprec$ is unique -- any other function satisfying the equations of the UP must be equal to $\simprec$.

~~~ {.mycelium}
theorem simprec-unique
if
  * ∀a. t(a)(\zero) == phi(a)
  * ∀a. (∀k. t(a)(\next(k)) == mu(a)(k)(t(a)(k)))
then
  * t == \simprec(phi)(mu)

proof
1.  ∀u. t(u)(\zero) == phi(u) : assumption 1
2.  t(a)(\zero) == phi(a) : forall-elim u -> a; 1
3.  t(a)(\zero) : chain
     == phi(a) : use reiterate; 2
     == \simprec(phi)(mu)(a)(\zero) : flop use simprec-zero;
4.    t(a)(n) == \simprec(phi)(mu)(a)(n) : hypothesis n
5.    ∀u. (∀k. t(u)(\next(k)) == mu(u)(k)(t(u)(k)))
       : assumption 2
6.    ∀k. t(a)(\next(k)) == mu(a)(k)(t(a)(k))
       : forall-elim u -> a; 5
7.    t(a)(\next(n)) == mu(a)(n)(t(a)(n))
       : forall-elim k -> n; 6
8.    t(a)(\next(n)) : chain
       == mu(a)(n)(t(a)(n)) : use reiterate; 7
       == mu(a)(n)(\simprec(phi)(mu)(a)(n))
          : hypothesis n at z in mu(a)(n)(z)
       == \simprec(phi)(mu)(a)(\next(n))
          : flop use simprec-next;
9.  (t(a)(n) == \simprec(phi)(mu)(a)(n)) =>
      (t(a)(\next(n)) == \simprec(phi)(mu)(a)(\next(n)))
     : discharge n; 8
10. ∀k. (t(a)(k) == \simprec(phi)(mu)(a)(k)) =>
      (t(a)(\next(k)) == \simprec(phi)(mu)(a)(\next(k)))
     : forall-intro n -> k; 9
11. ∀k. t(a)(k) == \simprec(phi)(mu)(a)(k)
     : invoke nat-induction
       [P :-> t(a)(_) == \simprec(phi)(mu)(a)(_)]; 3, 10
12. t(a) == \simprec(phi)(mu)(a) : use fun-eq; 11
13. ∀k. t(k) == \simprec(phi)(mu)(k) : forall-intro a -> k; 12
14. t == \simprec(phi)(mu) : use fun-eq; 13
~~~

To recap, what we've done here is define a recursion operator $\simprec$ that can be characterized succinctly as the unique solution to a system of functional equations. What's useful about this is that $\simprec$ is now a prepackaged recursion pattern, and if we encounter (or want to define) recursive functions that match this pattern, we can use the universal property to reason about them. The hard part of that reasoning is neatly hidden away.
