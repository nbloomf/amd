---
title: Unit
---

Our first inductive type is called $\Unit$, and represents a type with only one inhabitant, called $\unit$ (lower case). So $\Unit$ has only one constructor, which takes no arguments.

~~~ {.mycelium}
type \unit :: Unit
~~~

There's not much we can do with a type having only one value. We can, however, define something like $\const$ with it.

~~~ {.mycelium}
type \only :: a -> Unit -> a
~~~

In fact $\Unit$ is the initial algebra of the constant functor to $\Unit$. Since it has "only one" inhabitant, functions from it to some type $a$ can be identified with values of type $a$, and $\only$ is precisely the universal map from $\Unit$ to some other $F$-algebra.

To use $\only$ and $\unit$ in this way, we need some inference rules to express that (1) $\only$ is an $F$-algebra morphism and (2) it is unique with this property.

Stating that $\only$ is a morphism is a little tricky since we've identified $a$ with functions $\Unit \rightarrow a$. But if we tilt our heads just right, and remember that $F(x) = \Unit$ and $F(f) = \id$, this diagram:

$$\require{AMScd}
\begin{CD}
F(\Unit) @>{\id}>> \Unit \\
@V{\id}VV @VV{\only(\const(a))}V \\
F(x) @>>{\const(a)}> x
\end{CD}$$

implies that "$\only(a)$ is an $F$-algebra homomorphism" should be stated like so:

~~~ {.mycelium}
rule only-unit
* \only(a)(\unit) == a
~~~

And for uniqueness, any map satisfying this property is equal to $\only$.

~~~ {.mycelium}
rule only-unit-unique
if
  * t(a)(\unit) == a
then
  * t == \only
~~~

Last but not least, every inductive type comes with an _induction principle_. For $\Unit$ this is not very interesting, but we'll include it as a template for later types. Essentially, the induction principle for an inductive type allows us to prove arbitrary statements by case analysis on the constructors of the type.

~~~ {.mycelium}
rule unit-induction
if
  * (x == \unit) => P
then
  * P
~~~

Again- $\Unit$ is an inauspicious place to start working with inductive types because there's not much to say about it. But it is a nice example of all the basic ingredients of an inductive type: constructors, the algebra map, the homomorphism property, the uniqueness property, and the induction principle. Unit will also be useful later.

Here's a theorem just for fun. This is fun, right?

~~~ {.mycelium}
theorem flip-only
* \flip(\only)(\unit) == \id

proof
1. \flip(\only)(\unit)(a) : chain
    == \only(a)(\unit) : use def-flip;
    == a : use only-unit;
    == \id(a) : flop use def-id;
2. ∀x. \flip(\only)(\unit)(x) == \id(x) : forall-intro a -> x; 1
3. \flip(\only)(\unit) == \id : use fun-eq; 2
~~~
