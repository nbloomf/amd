---
title: Basics
---

In these pages we'll be writing lots of proofs using _natural deduction_. A complete tutorial on natural deduction is beyond our scope, but two of its features are important to us. First, it is similar to the way we reason informally (hence the name _natural_). Second, natural deduction proofs can be mechanically checked for correctness using a very simple algorithm.



Judgements
----------

The basic unit of a natural deduction proof is the _judgement_. Judgements are statements that may or may not be supported by _evidence_, which comes in the form of an _inference rule_. Inference rules are sometimes visualized using a tableau. Here's a very simple example.

$$\begin{array}{c}
P \\ \hline
P
\end{array}$$

In this table, $P$ is a _judgement variable_. The $P$ above the line is called a _premise_ of the rule, and the one below is called the _consequence_ of the rule. In words, this rule says:

_If we have evidence supporting $P$, then we have evidence supporting $P$._

Profound! I'm going to state this one more time, using slightly different syntax.

~~~ {.mycelium}
rule reiterate
if
  * P
then
  * P
~~~

Here we've also given this rule a name: _reiterate_. This syntax is understood by a special tool that knows how to check natural deduction proofs. We'll revisit this point later.



Compound Judgements
-------------------

We can think of the judgement variable $P$ above as a _simple_ judgement. It is also possible to form _compound_ judgements using the _unary_ symbol $\neg$ and the _binary_ symbols $\wedge$, $\vee$, $\Rightarrow$, and $\Leftrightarrow$. For example, if $P$, $Q$, and $R$ are judgements, then the following strings of symbols are also judgements.

$$\begin{array}{ccc}
P \wedge Q & \neg P & P \vee Q \\
P \Rightarrow Q & (P \wedge Q) \Leftrightarrow \neg R & P \vee (Q \vee R)
\end{array}$$

If you've read about formal logic before (and I suspect you have) you'll recognize these symbols as meaning _not_, _and_, _or_, _implies_, and _iff_. But here it's important that we not imbue the symbols with meaning, at least not yet.

We can use inference rules to govern the behavior of each of these symbols, and that behavior _is_ the meaning of the logical symbols. To be systematic about it, each symbol has one or more _introduction_ rules, where the symbol appears in the consequence, and one or more _elimination_ rules, where the symbol appears among the premises. Some of these inference rules are baked into the checking tool for reasons we'll explain as we go. But most of them can be defined like `reiterate` above.

For example, here is the elimination rule for $\Rightarrow$.

$$\begin{array}{ccc}
P &   & P \Rightarrow Q \\ \hline
  & Q &
\end{array}$$

Note how $\Rightarrow$ appears above the line (i.e. in the premises) but not below (in the consequence).

~~~ {.mycelium}
rule impl-elim
if
  * P
  * P => Q
then
  * Q
~~~



Proof
-----

A _proof_ is a list of judgements, each supported by evidence: either a reference to an inference rule, or an explicit assumption. A proof is _valid_ if each step is valid; an invoked inference rule is valid if it can be matched against the referenced lines in the proof, and assumptions are always valid.

If a proof is valid, then its last line and assumptions become the consequence and premises of a new _derived_ inference rule, a.k.a., a theorem.

Let's look at an example.

~~~ {.mycelium}
theorem impl-elim-2
if
  * P
  * P => Q
  * Q => R
then
  * R

proof
1. P : assumption 1
2. P => Q : assumption 2
3. Q : use impl-elim; 1, 2
4. Q => R : assumption 3
5. R : use impl-elim; 3, 4
~~~

We're using the goofy syntax again, but this is reasonably readable. It looks like the inference rules, but now we have a `proof` block. Each line in the proof has a label, a judgement, and evidence. Assumptions are numbered as they appear in the premises of the theorem, and `use` refers to a known inference rule, in this case the $\Rightarrow$-elimination rule.

Notably, this proof is _machine checked_. We have a program that parses this text, extracts the inference rules, and validates the proof. Does this mean the proofs are guaranteed to have no errors? No; there could always be a bug in the checking tool. But computers never get bored or tired of pushing symbols around. Checked proofs are much less likely to have errors than those written only for human readers as long as we're careful that the checker is working correctly.

I mentioned that inference rules should come in elimination/introduction pairs. So, what is the introduction rule for $\Rightarrow$? This is one of the special cases, and involves two different kinds of evidence. The best way to see this is with an example.

~~~ {.mycelium}
theorem syllogism
if
  * P => Q
  * Q => R
then
  * P => R

proof
1.   P : hypothesis hyp-P
2.   P => Q : assumption 1
3.   Q => R : assumption 2
4.   R : use impl-elim-2; 1, 2, 3
5. P => R : discharge hyp-P; 4
~~~

This proof introduces two new kinds of evidence: `hypothesis` and `discharge`. Together these are the introduction rule for $\Rightarrow$. `hypothesis` lets us pull a supported judgement out of thin air, but this comes with a price: the hypothesis must be `discharge`d before the proof is done, and the judgement must appear on the left of a $\Rightarrow$. Hypotheses are also given a name (`hyp-P` here) so we can tell them apart.

Typically when writing natural deduction proofs hypotheses and statements that depend on them are indented, to help us remember that they need to be discharged. The proof checking tool doesn't need this, but it's easier on human eyes, and makes writing the proof easier, as the indentation level acts like a natural "stack" of undischarged proof obligations.

Hypotheses and assumptions are similar; both let us pull judgements out of nowhere. But hypotheses must be discharged and can't be used again after that, while assumptions are never discharged. Here's another example.

~~~ {.mycelium}
theorem impl-idemp
* P => P

proof
1.   P : hypothesis hyp-P
2. P => P : discharge hyp-P; 1
~~~
