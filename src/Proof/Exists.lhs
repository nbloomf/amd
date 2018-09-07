---
title: Existential Quantification
---

We also have built in introduction and elimination rules for the existential quantifier. The introduction rule looks like

$$\begin{array}{c}
\Phi[u \mapsto e] \\ \hline
\exists u . \Phi
\end{array}$$

with no side conditions, while the elimination rule is

$$\begin{array}{c}
\exists x. \Phi & & \Phi[x \mapsto u] \Rightarrow \Psi \\ \hline
 & \Psi &
\end{array}$$

with the side conditions that $u$ does not occur in $\exists x . \Phi$, in $\Psi$, or in any undischarged hypotheses or assumptions in the proof of $\Phi[x \mapsto u] \Rightarrow \Psi$.

~~~ {.mycelium}
theorem exists-conj
if
  * ∃k. (P /\ Q)
then
  * (∃k. P) /\ (∃k. Q)

proof
1. ∃k. (P /\ Q) : assumption 1
2.   P /\ Q : hypothesis PQ
3.   P : use conj-elim-l; 2
4.   ∃k. P : exists-intro k <- u; 3
5.   Q : use conj-elim-r; 2
6.   ∃k. Q : exists-intro k <- u; 5
7.   (∃k. P) /\ (∃k. Q) : use conj-intro; 4, 6
8. (P /\ Q) => ((∃k. P) /\ (∃k. Q)) : discharge PQ; 7
9. (∃k. P) /\ (∃k. Q) : exists-elim u <- k; 1, 8
~~~
