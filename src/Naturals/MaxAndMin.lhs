---
title: Max and Min
---

~~~ {.mycelium}
type \max :: Nat -> Nat -> Nat

definition def-max
* \max(a)(b) == \if(b)(a)(\leq(a)(b))


type \min :: Nat -> Nat -> Nat

definition def-min
* \min(a)(b) == \if(a)(b)(\leq(a)(b))
~~~


~~~ {.mycelium}
theorem max-idemp
* \max(a)(a) == a

proof
1. \max(a)(a) : chain
    == \if(a)(a)(\leq(a)(a))
     : use def-max;
    == \if(a)(a)(\true)
     : use leq-refl; at z in
       \if(a)(a)(z)
    == a
     : use if-true;


theorem min-idemp
* \min(a)(a) == a

proof
1. \min(a)(a) : chain
    == \if(a)(a)(\leq(a)(a))
     : use def-min;
    == \if(a)(a)(\true)
     : use leq-refl; at z in
       \if(a)(a)(z)
    == a
     : use if-true;
~~~

~~~ {.mycelium}
theorem max-zero-l
* \max(\zero)(a) == a

proof
1. \max(\zero)(a) : chain
    == \if(a)(\zero)(\leq(\zero)(a))
     : use def-max;
    == \if(a)(\zero)(\true)
     : use leq-zero-l; at z in
       \if(a)(\zero)(z)
    == a
     : use if-true;


theorem min-zero-l
* \min(\zero)(a) == \zero

proof
1. \min(\zero)(a) : chain
    == \if(\zero)(a)(\leq(\zero)(a))
     : use def-min;
    == \if(\zero)(a)(\true)
     : use leq-zero-l; at z in
       \if(\zero)(a)(z)
    == \zero
     : use if-true;
~~~

~~~ {.mycelium}
theorem max-next-next
* \max(\next(a))(\next(b)) == \next(\max(a)(b))

proof
1. \max(\next(a))(\next(b)) : chain
    == \if(\next(b))(\next(a))(\leq(\next(a))(\next(b)))
     : use def-max;
    == \if(\next(b))(\next(a))(\leq(a)(b))
     : use leq-next-next; at z in
       \if(\next(b))(\next(a))(z)
    == \next(\if(b)(a)(\leq(a)(b)))
     : use if-ap;
    == \next(\max(a)(b))
     : flop use def-max; at z in
       \next(z)


theorem min-next-next
* \min(\next(a))(\next(b)) == \next(\min(a)(b))

proof
1. \min(\next(a))(\next(b)) : chain
    == \if(\next(a))(\next(b))(\leq(\next(a))(\next(b)))
     : use def-min;
    == \if(\next(a))(\next(b))(\leq(a)(b))
     : use leq-next-next; at z in
       \if(\next(a))(\next(b))(z)
    == \next(\if(a)(b)(\leq(a)(b)))
     : use if-ap;
    == \next(\min(a)(b))
     : flop use def-min; at z in
       \next(z)
~~~
