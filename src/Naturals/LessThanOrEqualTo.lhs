---
title: Less Than or Equal To
---

~~~ {.mycelium}
type \leq :: Nat -> Nat -> Bool

definition def-leq
* \leq(a)(b) == \opt(\false)(\const(\true))(\minus(b)(a))
~~~


~~~ {.mycelium}
theorem leq-refl
* \leq(a)(a) == \true

proof
1. \leq(a)(a) : chain
    == \opt(\false)(\const(\true))(\minus(a)(a))
        : use def-leq;
    == \opt(\false)(\const(\true))(\just(\zero))
        : use minus-self; at z in \opt(\false)(\const(\true))(z)
    == \const(\true)(\zero) : use opt-just;
    == \true : use def-const;
~~~



 ~~~ {.mycelium}
theorem leq-impl-plus
if
  * \leq(a)(b) == \true
then
  * ∃k. b == \plus(a)(k)

proof
1. (\minus(b)(a) == \nothing) \/ (∃u. \minus(b)(a) == \just(u)) : use maybe-cases;
2.   \minus(b)(a) == \nothing : hypothesis nothing
3.   
~~~
