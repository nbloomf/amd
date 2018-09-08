---
title: Identity and Composition
---

The object language of our logic is _simply typed lambda calculus_. Later we'll start defining interesting types, but to begin we need to define some basic, generic functions.

Before we get too far, we need to nail down what it means for two functions to be equal. First, lets think about one of the _consequences_ of two functions being equal.

~~~ {.mycelium}
theorem fun-ap
if
  * f == g
then
  * f(x) == g(x)

proof
1. f == g : assumption 1
2. f(x) == f(x) : eq-intro
3. f(x) == g(x) : eq-elim h (f(x) == h(x)); 1, 2
~~~

~~~ {.mycelium}
theorem ap-eq
if
  * x == y
then
  * f(x) == f(y)

proof
1. x == y : assumption 1
2. f(x) : chain
    == f(y) : assumption 1 at z in f(z)
~~~

That is, if two functions are equal, then their outputs are equal for any given input. We'll say that this goes both ways.

~~~ {.mycelium}
rule fun-eq
if
  * ∀x. f(x) == g(x)
then
  * f == g
~~~

(Here's a helper theorem we'll need later.)

~~~ {.mycelium}
theorem fun-ap-2
if
  * f == g
then
  * f(x)(y) == g(x)(y)

proof
1. f == g : assumption 1
2. f(x) == g(x) : use fun-ap; 1
3. f(x)(y) == g(x)(y) : use fun-ap; 2
~~~

The simplest function is the _identity_, which takes an input and returns it unchanged.

~~~ {.mycelium}
type \id :: a -> a

definition def-id
* \id(x) == x
~~~

There's not a whole lot we can do with the identity function by itself, but things get a little more interesting when we can _compose_ functions. If $f : a \rightarrow b$ and $g : b \rightarrow c$ are functions, then their composite $g \circ f$ is the function $a \rightarrow c$ that applies $g$ to the output of $f$.

~~~ {.mycelium}
type \comp :: (b -> c) -> (a -> b) -> a -> c

definition def-comp
* \comp(g)(f)(a) == g(f(a))
~~~

Composition is a partial multiplication on functions, and the identity function is its neutral element. Functions are unchanged when we compose with identity from the left:

~~~ {.mycelium}
theorem comp-id-l
* \comp(\id)(f) == f

proof
1. \comp(\id)(f)(a) : chain
    == \id(f(a)) : use def-comp;
    == f(a) : use def-id;
2. ∀x. \comp(\id)(f)(x) == f(x) : forall-intro a -> x; 1
3. \comp(\id)(f) == f : use fun-eq; 2
~~~

As well as from the right.

~~~ {.mycelium}
theorem comp-id-r
* \comp(f)(\id) == f

proof
1. \comp(f)(\id)(a) : chain
    == f(\id(a)) : use def-comp;
    == f(a) : use def-id; at z in f(z)
2. ∀x. \comp(f)(\id)(x) == f(x) : forall-intro a -> x; 1
3. \comp(f)(\id) == f : use fun-eq; 2
~~~

We can also reify function application with $\app$.

~~~ {.mycelium}
type \app :: (a -> b) -> a -> b

rule def-app
* \app(f)(x) == f(x)
~~~

Now $\app$ distributes over $\comp$.

~~~ {.mycelium}
theorem app-comp-dist-l
* \app(\comp(g)(f)) == \comp(\app(g))(\app(f))

proof
1. \app(\comp(g)(f))(x) : chain
    == \comp(g)(f)(x) : use def-app;
    == g(f(x)) : use def-comp;
    == \app(g)(f(x)) : flop use def-app;
    == \app(g)(\app(f)(x)) : flop use def-app; at z in \app(g)(z)
    == \comp(\app(g))(\app(f))(x) : flop use def-comp;
2. ∀u. \app(\comp(g)(f))(u) == \comp(\app(g))(\app(f))(u)
    : forall-intro x -> u; 1
3. \app(\comp(g)(f)) == \comp(\app(g))(\app(f)) : use fun-eq; 2
~~~
