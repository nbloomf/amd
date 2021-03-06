---
title: Pair
---

We'll be needing a couple of special types with two type parameters, representing products and sums. Given types $a$ and $b$, there is a type $\Pair\ a\ b$ with two mappings $\fst : \Pair\ a\ b \rightarrow a$ and $\snd : \Pair\ a\ b \rightarrow b$ with the property that if $x$ is a type and we have morphisms $\sigma : x \rightarrow a$ and $\tau : x \rightarrow b$, then there is a unique morphism $\pair(\sigma)(\tau) : x \rightarrow \Pair\ a\ b$ making the following diagram commute.

$$\require{AMScd}
\begin{CD}
x @= x @= x \\
@V{\sigma}VV @VV{\pair(\sigma)(\tau)}V @VV{\tau}V \\
a @<<{\fst}< \Pair\ a\ b @>>{\snd}> b
\end{CD}$$

I think it is possible to fit this type into the framework of extremal $F$-algebras, but for now we'll just characterize this universal property in a more ad-hoc way. First we have the types of $\fst$, $\snd$, and $\pair$.

~~~ {.mycelium}
type \fst :: Pair a b -> a

type \snd :: Pair a b -> b

type \pair :: (t -> a) -> (t -> b) -> t -> Pair a b
~~~

And we have the homomorphism property of $\pair$.

~~~ {.mycelium}
rule fst-pair
* \fst(\pair(f)(g)(t)) == f(t)

rule snd-pair
* \snd(\pair(f)(g)(t)) == g(t)
~~~

Finally, $\pair$ is unique.

~~~ {.mycelium}
rule pair-unique
if
  * \comp(\fst)(h) == f
  * \comp(\snd)(h) == g
then
  * h == \pair(f)(g)
~~~

And we have a sort of induction principle for pairs.

~~~ {.mycelium}
rule pair-analysis
if
  * ∀t. P[_1 :-> \fst(t); _2 :-> \snd(t)]
then
  * ∀u. (∀v. P[_1 :-> u; _2 :-> v])
~~~

From uniqueness, we can characterize $\id$ in terms of $\pair$.

~~~ {.mycelium}
theorem pair-fst-snd
* \id == \pair(\fst)(\snd)

proof
1. \comp(\fst)(\id)(x) : chain
    == \fst(\id(x)) : use def-comp;
    == \fst(x) : use def-id; at z in \fst(z)
2. ∀t. \comp(\fst)(\id)(t) == \fst(t) : forall-intro x -> t; 1
3. \comp(\fst)(\id) == \fst : use fun-eq; 2
4. \comp(\snd)(\id)(x) : chain
    == \snd(\id(x)) : use def-comp;
    == \snd(x) : use def-id; at z in \snd(z)
5. ∀t. \comp(\snd)(\id)(t) == \snd(t) : forall-intro x -> t; 4
6. \comp(\snd)(\id) == \snd : use fun-eq; 5
7. \id == \pair(\fst)(\snd) : use pair-unique; 3, 6
~~~

Composition distributes over pair from the right.

~~~ {.mycelium}
theorem comp-pair-dist-r
* \comp(\pair(f)(g))(w) == \pair(\comp(f)(w))(\comp(g)(w))

proof
1. \comp(\fst)(\comp(\pair(f)(g))(w))(x) : chain
    == \fst(\comp(\pair(f)(g))(w)(x)) : use def-comp;
    == \fst(\pair(f)(g)(w(x))) : use def-comp; at z in \fst(z)
    == f(w(x)) : use fst-pair;
    == \comp(f)(w)(x) : flop use def-comp;
2. ∀t. \comp(\fst)(\comp(\pair(f)(g))(w))(t) == \comp(f)(w)(t)
    : forall-intro x -> t; 1
3. \comp(\fst)(\comp(\pair(f)(g))(w)) == \comp(f)(w) : use fun-eq; 2
4. \comp(\snd)(\comp(\pair(f)(g))(w))(x) : chain
    == \snd(\comp(\pair(f)(g))(w)(x)) : use def-comp;
    == \snd(\pair(f)(g)(w(x))) : use def-comp; at z in \snd(z)
    == g(w(x)) : use snd-pair;
    == \comp(g)(w)(x) : flop use def-comp;
5. ∀t. \comp(\snd)(\comp(\pair(f)(g))(w))(t) == \comp(g)(w)(t)
    : forall-intro x -> t; 4
6. \comp(\snd)(\comp(\pair(f)(g))(w)) == \comp(g)(w) : use fun-eq; 5
7. \comp(\pair(f)(g))(w) == \pair(\comp(f)(w))(\comp(g)(w))
    : use pair-unique; 3, 6
~~~

On the face of it, we don't have a way to actually "construct" values of type $\Pair\ a\ b$ -- but in fact we can, with $\pair$.

~~~ {.mycelium}
type \tup :: a -> b -> Pair a b

rule def-tup
* \tup(a)(b) == \pair(\only(a))(\only(b))(\unit)
~~~

We'll need a lemma about the interaction between $\pair$ and $\only$.

~~~ {.mycelium}
theorem pair-only
* \comp(\pair(f)(g))(\only(t)) == \pair(\only(f(t)))(\only(g(t)))

proof
1. \comp(\fst)(\comp(\pair(f)(g))(\only(t)))(\unit) : chain
    == \fst(\comp(\pair(f)(g))(\only(t))(\unit)) : use def-comp;
    == \fst(\pair(f)(g)(\only(t)(\unit))) : use def-comp; at z in \fst(z)
    == f(\only(t)(\unit)) : use fst-pair;
    == f(t) : use only-unit; at z in f(z)
    == \only(f(t))(\unit) : flop use only-unit;
2. ∀u. \comp(\fst)(\comp(\pair(f)(g))(\only(t)))(u) == \only(f(t))(u)
    : invoke unit-induction [P :-> \comp(\fst)(\comp(\pair(f)(g))(\only(t)))(_) == \only(f(t))(_)]; 1
3. \comp(\fst)(\comp(\pair(f)(g))(\only(t))) == \only(f(t)) : use fun-eq; 2
4. \comp(\snd)(\comp(\pair(f)(g))(\only(t)))(\unit) : chain
    == \snd(\comp(\pair(f)(g))(\only(t))(\unit)) : use def-comp;
    == \snd(\pair(f)(g)(\only(t)(\unit))) : use def-comp; at z in \snd(z)
    == g(\only(t)(\unit)) : use snd-pair;
    == g(t) : use only-unit; at z in g(z)
    == \only(g(t))(\unit) : flop use only-unit;
5. ∀u. \comp(\snd)(\comp(\pair(f)(g))(\only(t)))(u) == \only(g(t))(u)
    : invoke unit-induction [P :-> \comp(\snd)(\comp(\pair(f)(g))(\only(t)))(_) == \only(g(t))(_)]; 4
6. \comp(\snd)(\comp(\pair(f)(g))(\only(t))) == \only(g(t)) : use fun-eq; 5
7. \comp(\pair(f)(g))(\only(t)) == \pair(\only(f(t)))(\only(g(t)))
    : use pair-unique; 3, 6
~~~

With the lemma, we can show that every value of type $\Pair\ a\ b$ is of the form $\tup(u)(v)$.

~~~ {.mycelium}
theorem tup-fst-snd
if
  * a == \fst(t)
  * b == \snd(t)
then
  * \tup(a)(b) == t

proof
1. a == \fst(t) : assumption 1
2. b == \snd(t) : assumption 2
3. \tup(a)(b) : chain
    == \tup(\fst(t))(b) : assumption 1 at z in \tup(z)(b)
    == \tup(\fst(t))(\snd(t)) : assumption 2 at z in \tup(\fst(t))(z)
    == \pair(\only(\fst(t)))(\only(\snd(t)))(\unit) : use def-tup;
    == \comp(\pair(\fst)(\snd))(\only(t))(\unit)
        : flop use pair-only; at h in h(\unit)
    == \pair(\fst)(\snd)(\only(t)(\unit)) : use def-comp;
    == \id(\only(t)(\unit))
        : flop use pair-fst-snd; at z in z(\only(t)(\unit))
    == \only(t)(\unit) : use def-id;
    == t : use only-unit;
~~~

Now the value $\tup(a)(b)$ behaves like an ordered pair, and $\fst$ and $\snd$ let us extract the "coordinates".

~~~ {.mycelium}
theorem fst-tup
* \fst(\tup(a)(b)) == a

proof
1. \fst(\tup(a)(b)) : chain
    == \fst(\pair(\only(a))(\only(b))(\unit))
        : use def-tup; at z in \fst(z)
    == \only(a)(\unit) : use fst-pair;
    == a : use only-unit;


theorem snd-tup
* \snd(\tup(a)(b)) == b

proof
1. \snd(\tup(a)(b)) : chain
    == \snd(\pair(\only(a))(\only(b))(\unit))
        : use def-tup; at z in \snd(z)
    == \only(b)(\unit) : use snd-pair;
    == b : use only-unit;
~~~

And we can characterize equality for pairs; they are equal precisely when their corresponding coordinates are equal

~~~ {.mycelium}
theorem tup-eq-1
if
  * \tup(a1)(b1) == \tup(a2)(b2)
then
  * (a1 == a2) /\ (b1 == b2)

proof
1. \tup(a1)(b1) == \tup(a2)(b2) : assumption 1
2. a1 : chain
    == \fst(\tup(a1)(b1)) : flop use fst-tup;
    == \fst(\tup(a2)(b2)) : assumption 1 at z in \fst(z)
    == a2 : use fst-tup;
3. b1 : chain
    == \snd(\tup(a1)(b1)) : flop use snd-tup;
    == \snd(\tup(a2)(b2)) : assumption 1 at z in \snd(z)
    == b2 : use snd-tup;
4. (a1 == a2) /\ (b1 == b2) : use conj-intro; 2, 3


theorem tup-eq-2
if
  * (a1 == a2) /\ (b1 == b2)
then
  * \tup(a1)(b1) == \tup(a2)(b2)

proof
1. (a1 == a2) /\ (b1 == b2) : assumption 1
2. a1 == a2 : use conj-elim-l; 1
3. b1 == b2 : use conj-elim-r; 1
4. \tup(a1)(b1) == \tup(a1)(b1) : eq-intro
5. \tup(a1)(b1) == \tup(a2)(b1)
    : eq-elim z (\tup(a1)(b1) == \tup(z)(b1)); 2, 4
6. b2 == b1 : use eq-sym; 3
7. \tup(a2)(b2) == \tup(a2)(b2) : eq-intro
8. \tup(a2)(b1) == \tup(a2)(b2)
    : eq-elim z (\tup(a2)(z) == \tup(a2)(b2)); 6, 7
9. \tup(a1)(b1) == \tup(a2)(b2) : use eq-trans; 5, 8
~~~

One more helper: we can explicitly decompose values of type $\Pair\ a\ b$ as tuples.

~~~ {.mycelium}
theorem tup-id
* \tup(\fst(x))(\snd(x)) == x

proof
1. \fst(x) == \fst(x) : eq-intro
2. \snd(x) == \snd(x) : eq-intro
3. \tup(\fst(x))(\snd(x)) == x : use tup-fst-snd; 1, 2
~~~

~~~ {.mycelium}
theorem pair-tup
* \tup(f(x))(g(x)) == \pair(f)(g)(x)

proof
1. f(x) : chain
    == \fst(\pair(f)(g)(x)) : flop use fst-pair;
2. g(x) : chain
    == \snd(\pair(f)(g)(x)) : flop use snd-pair;
3. \tup(f(x))(g(x)) == \pair(f)(g)(x) : use tup-fst-snd; 1, 2
~~~

~~~ {.mycelium}
type \uncurry :: (a -> b -> c) -> Pair a b -> c

definition def-uncurry
* \uncurry(f)(x) == f(\fst(x))(\snd(x))
~~~

~~~ {.mycelium}
theorem uncurry-tup
* \uncurry(f)(\tup(a)(b)) == f(a)(b)

proof
1. \uncurry(f)(\tup(a)(b)) : chain
    == f(\fst(\tup(a)(b)))(\snd(\tup(a)(b))) : use def-uncurry;
    == f(a)(\snd(\tup(a)(b))) : use fst-tup; at z in f(z)(\snd(\tup(a)(b)))
    == f(a)(b) : use snd-tup; at z in f(a)(z)
~~~
