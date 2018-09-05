---
title: Conjunction and Disjunction
---

The two most basic judgement constructors are _conjunction_ and _disjunction_. The conjunction of judgements $P$ and $Q$ is denoted $P \wedge Q$, and models _both and_: if we have evidence for _both_ $P$ _and_ $Q$, this is valid evidence for the conjunction $P \wedge Q$.

~~~ {.mycelium}
rule conj-intro
if
  * P
  * Q
then
  * P /\ Q
~~~

Conjunction has two elimination rules, one for extracting each side.

~~~ {.mycelium}
rule conj-elim-l
if
  * P /\ Q
then
  * P

rule conj-elim-r
if
  * P /\ Q
then
  * Q
~~~

With just the introduction and elimination rules for $\wedge$, we can prove some theorems. First -- conjunction is idempotent on judgements.

~~~ {.mycelium}
theorem conj-idem
if
  * P
then
  * P /\ P

proof
1. P : assumption 1
2. P /\ P : use conj-intro; 1, 1
~~~

Conjunction is commutative.

~~~ {.mycelium}
theorem conj-comm
if
  * P /\ Q
then
  * Q /\ P

proof
1. P /\ Q : assumption 1
2. P : use conj-elim-l; 1
3. Q : use conj-elim-r; 1
4. Q /\ P : use conj-intro; 3, 2
~~~

Conjunction is associative. This property comes in two forms -- associativity to the left:

~~~ {.mycelium}
theorem conj-assoc-l
if
  * P /\ (Q /\ R)
then
  * (P /\ Q) /\ R

proof
1. P /\ (Q /\ R) : assumption 1
2. P : use conj-elim-l; 1
3. Q /\ R : use conj-elim-r; 1
4. Q : use conj-elim-l; 3
5. R : use conj-elim-r; 3
6. P /\ Q : use conj-intro; 2, 4
7. (P /\ Q) /\ R : use conj-intro; 6, 5
~~~

And associativity to the right.

~~~ {.mycelium}
theorem conj-assoc-r
if
  * (P /\ Q) /\ R
then
  * P /\ (Q /\ R)

proof
1. (P /\ Q) /\ R : assumption 1
2. P /\ Q : use conj-elim-l; 1
3. P : use conj-elim-l; 2
4. Q : use conj-elim-r; 2
5. R : use conj-elim-r; 1
6. Q /\ R : use conj-intro; 4, 5
7. P /\ (Q /\ R) : use conj-intro; 3, 6
~~~

Where conjunction models _both and_, disjunction models _either or_. If we have evidence for _either_ $P$ _or_ $Q$, this is valid evidence for $P \vee Q$.

~~~ {.mycelium}
rule disj-intro-l
if
  * P
then
  * P \/ Q

rule disj-intro-r
if
  * Q
then
  * P \/ Q
~~~

The elimination rule for disjunction is a little different. We can think of it as _proof by case analysis_.

~~~ {.mycelium}
rule disj-elim
if
  * P \/ Q
  * P => R
  * Q => R
then
  * R
~~~

Disjunction has properties analogous to those of conjunction. It is idempotent:

~~~ {.mycelium}
theorem disj-idem
if
  * P
then
  * P \/ P

proof
1. P : assumption 1
2. P \/ P : use disj-intro-l; 1
~~~

Disjunction is commutative:

~~~ {.mycelium}
theorem disj-comm
if
  * P \/ Q
then
  * Q \/ P

proof
1. P \/ Q : assumption 1
2.   P : hypothesis hyp-P
3.   Q \/ P : use disj-intro-r; 2
4. P => (Q \/ P) : discharge hyp-P; 3
5.   Q : hypothesis hyp-Q
6.   Q \/ P : use disj-intro-l; 5
7. Q => (Q \/ P) : discharge hyp-Q; 6
8. Q \/ P : use disj-elim; 1, 4, 7
~~~

It associates to the left:

~~~ {.mycelium}
theorem disj-assoc-l
if
  * P \/ (Q \/ R)
then
  * (P \/ Q) \/ R

proof
1.  P \/ (Q \/ R) : assumption 1
2.    P : hypothesis hyp-P
3.    P \/ Q : use disj-intro-l; 2
4.    (P \/ Q) \/ R : use disj-intro-l; 3
5.  P => (P \/ Q) \/ R : discharge hyp-P; 4
6.    Q \/ R : hypothesis hyp-QR
7.      Q : hypothesis hyp-Q
8.      P \/ Q : use disj-intro-r; 7
9.      (P \/ Q) \/ R : use disj-intro-l; 8
10.   Q => (P \/ Q) \/ R : discharge hyp-Q; 9
11.     R : hypothesis hyp-R
12.     (P \/ Q) \/ R : use disj-intro-r; 11
13.   R => (P \/ Q) \/ R : discharge hyp-R; 12
14.   (P \/ Q) \/ R : use disj-elim; 6, 10, 13
15. Q \/ R => (P \/ Q) \/ R : discharge hyp-QR; 14
16. (P \/ Q) \/ R : use disj-elim; 1, 5, 15
~~~

And it associates to the right:

~~~ {.mycelium}
theorem disj-assoc-r
if
  * (P \/ Q) \/ R
then
  * P \/ (Q \/ R)

proof
1.  (P \/ Q) \/ R : assumption 1
2.    P \/ Q : hypothesis hyp-PQ
3.      P : hypothesis hyp-P
4.      P \/ (Q \/ R) : use disj-intro-l; 3
5.    P => P \/ (Q \/ R) : discharge hyp-P; 4
6.      Q : hypothesis hyp-Q
7.      Q \/ R : use disj-intro-l; 6
8.      P \/ (Q \/ R) : use disj-intro-r; 7
9.    Q => P \/ (Q \/ R) : discharge hyp-Q; 8
10.   P \/ (Q \/ R) : use disj-elim; 2, 5, 9
11. P \/ Q => P \/ (Q \/ R) : discharge hyp-PQ; 10
12.   R : hypothesis hyp-R
13.   Q \/ R : use disj-intro-r; 12
14.   P \/ (Q \/ R) : use disj-intro-r; 13
15. R => P \/ (Q \/ R) : discharge hyp-R; 14
16. P \/ (Q \/ R) : use disj-elim; 1, 11, 15
~~~

Conjunction and disjunction also interact with each other. Specifically, each distributes over the other from both sides.

First we show that conjunction distributes over disjunction from the left.

~~~ {.mycelium}
theorem conj-disj-dist-l
if
  * P /\ (Q \/ R)
then
  * (P /\ Q) \/ (P /\ R)

proof
1.  P /\ (Q \/ R) : assumption 1
2.  P : use conj-elim-l; 1
3.  Q \/ R : use conj-elim-r; 1
4.   Q : hypothesis hyp-Q
5.   P /\ Q : use conj-intro; 2, 4
6.   (P /\ Q) \/ (P /\ R) : use disj-intro-l; 5
7.  Q => (P /\ Q) \/ (P /\ R) : discharge hyp-Q; 6
8.   R : hypothesis hyp-R
9.   P /\ R : use conj-intro; 2, 8
10.  (P /\ Q) \/ (P /\ R) : use disj-intro-r; 9
11. R => (P /\ Q) \/ (P /\ R) : discharge hyp-R; 10
12. (P /\ Q) \/ (P /\ R) : use disj-elim; 3, 7, 11
~~~

Next we show that conjunction distributes over disjunction from the right. We could do this with a proof analogous to the left-hand case, but we take a different strategy that ends up being the same length.

~~~ {.mycelium}
theorem conj-disj-dist-r
if
  * (P \/ R) /\ Q
then
  * (P /\ Q) \/ (R /\ Q)

proof
1.  (P \/ R) /\ Q : assumption 1
2.  Q /\ (P \/ R) : use conj-comm; 1
3.  (Q /\ P) \/ (Q /\ R) : use conj-disj-dist-l; 2
4.    Q /\ P : hypothesis hyp-QP
5.    P /\ Q : use conj-comm; 4
6.    (P /\ Q) \/ (R /\ Q) : use disj-intro-l; 5
7.  Q /\ P => (P /\ Q) \/ (R /\ Q) : discharge hyp-QP; 6
8.    Q /\ R : hypothesis hyp-QR
9.    R /\ Q : use conj-comm; 8
10.   (P /\ Q) \/ (R /\ Q) : use disj-intro-r; 9
11. Q /\ R => (P /\ Q) \/ (R /\ Q) : discharge hyp-QR; 10
12. (P /\ Q) \/ (R /\ Q) : use disj-elim; 3, 7, 11
~~~

Disjunction also distributes over conjunction from the left:

~~~ {.mycelium}
theorem disj-conj-dist-l
if
  * P \/ (Q /\ R)
then
  * (P \/ Q) /\ (P \/ R)

proof
1.  P \/ (Q /\ R) : assumption 1
2.    P : hypothesis hyp-P
3.    P \/ Q : use disj-intro-l; 2
4.    P \/ R : use disj-intro-l; 2
5.    (P \/ Q) /\ (P \/ R) : use conj-intro; 3, 4
6.  P => (P \/ Q) /\ (P \/ R) : discharge hyp-P; 5
7.    Q /\ R : hypothesis hyp-QR
8.    Q : use conj-elim-l; 7
9.    P \/ Q : use disj-intro-r; 8
10.   R : use conj-elim-r; 7
11.   P \/ R : use disj-intro-r; 10
12.   (P \/ Q) /\ (P \/ R) : use conj-intro; 9, 11
13. Q /\ R => (P \/ Q) /\ (P \/ R) : discharge hyp-QR; 12
14. (P \/ Q) /\ (P \/ R) : use disj-elim; 1, 6, 13
~~~

And from the right.

~~~ {.mycelium}
theorem disj-conj-dist-r
if
  * (P /\ Q) \/ R
then
  * (P \/ R) /\ (Q \/ R)

proof
1. (P /\ Q) \/ R : assumption 1
2. R \/ (P /\ Q) : use disj-comm; 1
3. (R \/ P) /\ (R \/ Q) : use disj-conj-dist-l; 2
4. R \/ P : use conj-elim-l; 3
5. P \/ R : use disj-comm; 4
6. R \/ Q : use conj-elim-r; 3
7. Q \/ R : use disj-comm; 6
8. (P \/ R) /\ (Q \/ R) : use conj-intro; 5, 7
~~~
