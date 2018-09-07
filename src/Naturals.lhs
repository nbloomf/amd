---
title: Natural Numbers
---

We can define the natural numbers $\Nat$ as the initial $F$-algebra for the functor $F(x) = \Either\ \Unit\ x$. The algebra map $m : \Either\ \Unit\ \Nat \rightarrow \Nat$ has two components, $\zero$ and $\next$.

~~~ {.mycelium}
type \zero :: Nat

type \next :: Nat -> Nat
~~~

And $\zero$ is not of the form $\next(n)$.

~~~ {.mycelium}
rule nat-disc
* ~(∃n. \zero == \next(n))
~~~

The unique homomorphism from $\Nat$ to some other $F$-algebra is denoted $\natrec$, and is the unique map making the following diagram commute.

$$\require{AMScd}
\begin{CD}
\Either\ \Unit\ \Nat @>{\either(\only(\zero))(\next)}>> \Nat \\
@V{\id}VV @VV{\natrec(e)(f)}V \\
\Either\ \Unit\ a @>>{\either(\only(e))(f)}> a
\end{CD}$$

The signature of $\natrec$ looks like this.

~~~ {.mycelium}
type \natrec :: a -> (a -> a) -> Nat -> a
~~~

We need rules to say that $\natrec$ is an $F$-algebra homomorphism:

~~~ {.mycelium}
rule natrec-zero
* \natrec(e)(f)(\zero) == e

rule natrec-next
* \natrec(e)(f)(\next(n)) == f(\natrec(e)(f)(n))
~~~

And a rule to say that $\natrec$ is unique.

~~~ {.mycelium}
rule natrec-unique
if
  * t(\zero) == e
  * \comp(t)(\next) == \comp(f)(t)
then
  * t == \natrec(e)(f)
~~~

Finally, we need an induction principle for $\Nat$.

~~~ {.mycelium}
rule nat-induction
if
  * (k == \zero) => P
  * ∀n. ((k == n) => P) => ((k == \next(n)) => P)
then
  * P
~~~

Using the uniqueness of $\natrec$, we can characterize $\id$ as an $F$-algebra homomorphism. This theorem essentially states that $$n = \underbrace{1 + 1 + \cdots + 1}_{n\ \mathrm{times}}$$

~~~ {.mycelium}
theorem natrec-zero-next
* \id == \natrec(\zero)(\next)

proof
1. \id(\zero) == \zero : use def-id;
2. \comp(\id)(\next) : chain
    == \next : use comp-id-l;
    == \comp(\next)(\id) : flop use comp-id-r;
3. \id == \natrec(\zero)(\next) : use natrec-unique; 1, 2
~~~

We can think of the induction principle on $\Nat$ as facilitating _proof by case analysis_; we can construct evidence for an arbitrary judgement $P$ by splitting the universe into two pieces and finding evidence for $P$ in each piece. This isn't the only useful kind of case analysis. For instance, we can show that every natural number is either $\zero$ or of the form $\next(k)$; this facilitates case analysis of a different sort.

~~~ {.mycelium}
theorem nat-disj-cases-1
* (a == \zero) \/ (∃k. a == \next(k))

proof
1.    a == \zero : hypothesis a-zero
2.    (a == \zero) \/ (∃k. a == \next(k)) : use disj-intro-l; 1
3.  (a == \zero) => ((a == \zero) \/ (∃k. a == \next(k)))
     : discharge a-zero; 2
4.      a == \next(n) : hypothesis a-next
5.      ∃k. a == \next(k) : exists-intro k <- n; 4
6.      (a == \zero) \/ (∃k. a == \next(k)) : use disj-intro-r; 5
7.  (a == \next(n)) => ((a == \zero) \/ (∃k. a == \next(k)))
     : discharge a-next; 6
8.  ((a == n) => ((a == \zero) \/ (∃k. a == \next(k)))) =>
      ((a == \next(n)) => ((a == \zero) \/ (∃k. a == \next(k))))
     : use simp; 7
9.  ∀t. ((a == t) => ((a == \zero) \/ (∃k. a == \next(k)))) =>
      ((a == \next(t)) => ((a == \zero) \/ (∃k. a == \next(k))))
     : forall-intro n -> t; 8
10. (a == \zero) \/ (∃k. a == \next(k)) : use nat-induction; 3, 9
~~~

It's also handy to state this result in a more general form.

~~~ {.mycelium}
theorem nat-cases-1
if
  * (a == \zero) => P
  * (∃k. a == \next(k)) => P
then
  * P

proof
1. (a == \zero) \/ (∃k. a == \next(k)) : use nat-disj-cases-1;
2. (a == \zero) => P : assumption 1
3. (∃k. a == \next(k)) => P : assumption 2
4. P : use disj-elim; 1, 2, 3
~~~

Similarly, every natural number is either $\zero$, $\next(\zero)$, or $\next(\next(k))$ for some $k$. This allows a three-way case analysis.

~~~ {.mycelium}
theorem nat-disj-cases-2
* (a == \zero) \/ ((a == \next(\zero)) \/ (∃k. a == \next(\next(k))))

proof
1.  (a == \zero) \/ (∃k. a == \next(k)) : use nat-disj-cases-1;
2.    a == \zero : hypothesis a-zero
3.    (a == \zero) \/ ((a == \next(\zero)) \/ (∃k. a == \next(\next(k)))) : use disj-intro-l; 2
4.  (a == \zero) => ((a == \zero) \/ ((a == \next(\zero)) \/ (∃k. a == \next(\next(k))))) : discharge a-zero; 3
5.    ∃k. a == \next(k) : hypothesis a-next
6.      a == \next(b) : hypothesis b
7.      (b == \zero) \/ (∃k. b == \next(k)) : use nat-disj-cases-1;
8.        b == \zero : hypothesis b-zero
9.        a : chain
           == \next(b) : hypothesis b
           == \next(\zero) : hypothesis b-zero at z in \next(z)
10.       (a == \next(\zero)) \/ (∃k. a == \next(\next(k))) : use disj-intro-l; 9
11.     (b == \zero) => ((a == \next(\zero)) \/ (∃k. a == \next(\next(k)))) : discharge b-zero; 10
12.       ∃k. b == \next(k) : hypothesis b-next
13.         b == \next(c) : hypothesis c
14.         a : chain
             == \next(b) : hypothesis b
             == \next(\next(c)) : hypothesis c at z in \next(z)
15.         ∃k. a == \next(\next(k)) : exists-intro k <- c; 14
16.       (b == \next(c)) => (∃k. a == \next(\next(k))) : discharge c; 15
17.       ∃k. a == \next(\next(k)) : exists-elim c <- k; 12, 16
18.       (a == \next(\zero)) \/ (∃k. a == \next(\next(k))) : use disj-intro-r; 17
19.     (∃k. b == \next(k)) => ((a == \next(\zero)) \/ (∃k. a == \next(\next(k)))) : discharge b-next; 18
20.     (a == \next(\zero)) \/ (∃k. a == \next(\next(k))) : use disj-elim; 7, 11, 19
21.     (a == \zero) \/ ((a == \next(\zero)) \/ (∃k. a == \next(\next(k)))) : use disj-intro-r; 20
22.   (a == \next(b)) => ((a == \zero) \/ ((a == \next(\zero)) \/ (∃k. a == \next(\next(k))))) : discharge b; 21
23.   (a == \zero) \/ ((a == \next(\zero)) \/ (∃k. a == \next(\next(k)))) : exists-elim b <- k; 5, 22
24. (∃k. a == \next(k)) => ((a == \zero) \/ ((a == \next(\zero)) \/ (∃k. a == \next(\next(k))))) : discharge a-next; 23
25. (a == \zero) \/ ((a == \next(\zero)) \/ (∃k. a == \next(\next(k)))) : use disj-elim; 1, 4, 24
~~~

We'll also state this in a more general form.

~~~ {.mycelium}
theorem nat-cases-2
if
  * (a == \zero) => P
  * (a == \next(\zero)) => P
  * (∃k. a == \next(\next(k))) => P
then
  * P

proof
1. (a == \zero) \/ ((a == \next(\zero)) \/ (∃k. a == \next(\next(k)))) : use nat-disj-cases-2;
2. (a == \zero) => P : assumption 1
3.   (a == \next(\zero)) \/ (∃k. a == \next(\next(k))) : hypothesis t
4.   (a == \next(\zero)) => P : assumption 2
5.   (∃k. a == \next(\next(k))) => P : assumption 3
6.   P : use disj-elim; 3, 4, 5
7. ((a == \next(\zero)) \/ (∃k. a == \next(\next(k)))) => P : discharge t; 6
8. P : use disj-elim; 1, 2, 7
~~~
