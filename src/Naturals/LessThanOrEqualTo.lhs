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
1.  (\minus(b)(a) == \nothing) \/ (∃u. \minus(b)(a) == \just(u))
     : use maybe-cases;

2.    \minus(b)(a) == \nothing : hypothesis nothing

3.    \true : chain
       == \leq(a)(b)
        : flop assumption 1
       == \opt(\false)(\const(\true))(\minus(b)(a))
        : use def-leq;
       == \opt(\false)(\const(\true))(\nothing)
        : hypothesis nothing at z in
          \opt(\false)(\const(\true))(z)
       == \false
        : use opt-nothing;

4.  (\minus(b)(a) == \nothing) => (\true == \false)
     : discharge nothing; 3

5.  ~(\true == \false) : use bool-disc;

6.  ~(\minus(b)(a) == \nothing) : use modus-tollens; 4, 5

7.  ∃u. \minus(b)(a) == \just(u) : use disj-syllogism-l; 1, 6

8.    \minus(b)(a) == \just(c) : hypothesis just

9.    b : chain
       == \plus(c)(a) : use minus-to-plus; 8
       == \plus(a)(c) : use plus-comm;


10.   ∃u. b == \plus(a)(u) : exists-intro u <- c; 9

11. (\minus(b)(a) == \just(c)) => (∃u. b == \plus(a)(u))
     : discharge just; 10

12. ∃u. b == \plus(a)(u) : exists-elim c <- u; 7, 11
~~~
