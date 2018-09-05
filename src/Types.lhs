---
title: Types
---

We'll be working with lots of concrete types, and for each one we'll need to introduce some new inference rules. It's important to make sure that introducing new inference rules doesn't also introduce a contradiction or otherwise collapse the logic to trivialness, and one of the best ways to do this is to be systematic about it.

Much like we systematically defined introduction and elimination rules for each judgement constructor, the rules we introduce for working with each new type will follow some specific patterns.

Before we get to the details, we need to say a few words about functors.

Our type grammar defines a category: the objects are types, and the arrows are values with arrow type. $\id$ and $\comp$ are the identity arrows and composites, respectively. So, for instance, if $a$ and $b$ are types, then a value $f$ with signature $a \rightarrow b$ is a morphism in the type category.

Suppose we have a functor $F$ on the type category. An $F$-algebra is an object (e.g. _type_) $x$ together with a distinguished arrow $\alpha : F(x) \rightarrow x$. Given two $F$-algebras $(x,\alpha)$ and $(y,\beta)$, an $F$-algebra morphism is a morphism $\theta : x \rightarrow y$ that makes the following square commute:

$$\require{AMScd}
\begin{CD}
F(x) @>{\alpha}>> x \\
@V{F(\theta)}VV @VV{\theta}V \\
F(y) @>>{\beta}> y
\end{CD}$$

To give a concrete example, $\Bool$ fits this pattern. We can think of $\Bool$ as representing a type with exactly two distinct values. It is the initial algebra of the constant functor $F(x) = \Bool$, and the universal arrow is given by $\if$.

$$\require{AMScd}
\begin{CD}
\Bool @>{\alpha(\true)(\false)}>> \Bool \\
@V{\id}VV @VV{\if(u)(v)}V \\
\Bool @>>{\beta(u)(v)}> x
\end{CD}$$

It turns out that the $F$-algebras again form a category, using this notion of morphism. And this category may have an initial object, which (if it exists) is unique up to a unique isomorphism.

We will call these initial $F$-algebras _inductive types_, and it turns out they can do some really cool stuff. Like, _really_ cool stuff.

And this is how we will systematically add new inference rules for reasoning about inductive types. The details will differ slightly in each case, but we'll always have:

1. A _type_, representing the initial $F$-algebra $\mathcal{A}$;
2. One or more _constructors_, representing the algebra map $F(\mathcal{A}) \rightarrow \mathcal{A}$;
3. One or more _discriminators_, showing that the constructors are distinct from each other;
4. A _destructor_, representing the unique algebra morphism $\mathcal{A} \rightarrow x$;
5. An _analysis principle_ for $\mathcal{A}$.

Taken together, these ingredients make it possible to define recursive types and carry out proofs by induction on them. The destructor is especially interesting; it will turn out to be "fold" on lists, "countdown" on natural numbers, and "if" on booleans.

Hopefully this will make more sense when we see some examples.
