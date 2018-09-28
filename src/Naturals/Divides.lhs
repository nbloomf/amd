---
title: Divides
---

~~~ {.mycelium}
type \div :: Nat -> Nat -> Bool

definition def-div
* \div(a)(b) == \eq(\zero)(\rem(b)(a))
~~~

~~~ {.mycelium}
theorem div-zero
* \div(a)(\zero) == \true

proof
1. \div(a)(\zero) : chain
    == \eq(\zero)(\rem(\zero)(a))
     : use def-div;
    == \eq(\zero)(\snd(\divalg(\zero)(a)))
     : use def-rem; at z in
       \eq(\zero)(z)
    == \eq(\zero)(\snd(\tup(\zero)(\zero)))
     : use divalg-zero-l; at z in
       \eq(\zero)(\snd(z))
    == \eq(\zero)(\zero)
     : use snd-tup; at z in
       \eq(\zero)(z)
    == \true
     : use eq-refl;
~~~
