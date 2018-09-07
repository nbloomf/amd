---
title: Negation
---

Negation is a little different. We're only interested in constructive proofs here, so our logic will not include the law of the excluded middle. This makes it _intuitionistic_. The intuitionistic introduction rule for negation looks sort of like proof by contradiction; if $P$ implies both $Q$ and not $Q$, then we must have not $P$.

~~~ {.mycelium}
rule neg-intro
if
  * P => Q
  * P => (~Q)
then
  * ~P
~~~

The intuitionistic elimination rule for negation looks a little bit like ex falso quodlibet (from false, anything is possible), although we should try not to think of judgements as true and false, but as supported and unsupported.

~~~ {.mycelium}
rule neg-elim
if
  * ~P
then
  * P => Q
~~~

One more theorem that doesn't really fit here, but we need it next and couldn't prove it before: the _simplification_ rule. If we have evidence for $P$, then we have evidence for the implication $Q \Rightarrow P$ for any $Q$.

~~~ {.mycelium}
theorem simp
if
  * P
then
  * Q => P

proof
1. P : assumption 1
2.   Q : hypothesis hyp-Q
3.   P /\ Q : use conj-intro; 1, 2
4.   P : use conj-elim-l; 3
5. Q => P : discharge hyp-Q; 4
~~~

Intuitionistic logic is very different from classical logic -- the basic difference is that we don't have the law of the excluded middle, so we can't prove $P$ by assuming $\neg P$ and getting a contradiction. We do have a version of the contraposition principle, though.

~~~ {.mycelium}
theorem contraposition
if
  * P => Q
then
  * (~Q) => (~P)

proof
1.   ~Q : hypothesis hyp-Q
2.   P => (~Q) : use simp; 1
3.   P => Q : assumption 1
4.   ~P : use neg-intro; 3, 2
5. (~Q) => (~P) : discharge hyp-Q; 4
~~~

A slightly more useful version of contraposition is called _modus tollens_.

~~~ {.mycelium}
theorem modus-tollens
if
  * P => Q
  * ~Q
then
  * ~P

proof
1. P => Q : assumption 1
2. ~Q : assumption 2
3. P => ~Q : use simp; 2
4. ~P : use neg-intro; 1, 3
~~~

Another handy tool is the _disjunctive syllogism_, which we'll give in two forms for convenience.

~~~ {.mycelium}
theorem disj-syllogism-l
if
  * P \/ Q
  * ~P
then
  * Q

proof
1. P \/ Q : assumption 1
2. ~P : assumption 2
3. P => Q : use neg-elim; 2
4. Q => Q : use impl-idemp;
5. Q : use disj-elim; 1, 3, 4


theorem disj-syllogism-r
if
  * P \/ Q
  * ~Q
then
  * P

proof
1. P \/ Q : assumption 1
2. Q \/ P : use disj-comm; 1
3. ~Q : assumption 2
4. P : use disj-syllogism-l; 2, 3
~~~
