---
title: Const
---

Here's a fun activity. Take a logical theorem involving only judgement variables and $\Rightarrow$, and try to turn it into a function signature. For example, the signature of $\id$ is $$a \rightarrow a$$ which is suspiciously similar to the `impl-idemp` theorem $$P \Rightarrow P.$$ Likewise the signature of $\comp$, $$(b \rightarrow c) \rightarrow (a \rightarrow b) \rightarrow a \rightarrow c$$ is similar to `impl-elim-2`, which can be restated as: $$(Q \Rightarrow R) \Rightarrow (P \Rightarrow Q) \Rightarrow P \Rightarrow R,$$ and $\app$, with signature $(a \rightarrow b) \rightarrow a \rightarrow b$, looks like the `impl-elim` rule.

This suggests that one way to come up with interesting functions is to start with a known theorem, turn it into a function signature, and do the most obvious thing. Another handy function we can construct this way is the constant function; this takes two inputs but ignores the second, returning the first unchanged.

~~~ {.mycelium}
type \const :: a -> b -> a

definition def-const
* \const(a)(b) == a
~~~

Now $\const$ absorbs under composition from the left.

~~~ {.mycelium}
theorem comp-const-l
* \comp(\const(a))(f) == \const(a)

proof
1. \comp(\const(a))(f)(x) : chain
    == \const(a)(f(x)) : use def-comp;
    == a : use def-const;
    == \const(a)(x) : flop use def-const;
2. ∀u. \comp(\const(a))(f)(u) == \const(a)(u) : forall-intro x -> u; 1
3. \comp(\const(a))(f) == \const(a) : use fun-eq; 2
~~~
