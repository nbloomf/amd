---
title: Minus
---

~~~ {.mycelium}
type \minusH :: Nat -> Nat -> Maybe Nat -> Maybe Nat

definition def-minus-helper
* \minusH(a)(b)(u) == \if(\just(\next(a)))(u)(\eq(\zero)(b))

type \minus :: Nat -> Nat -> Maybe Nat

definition def-minus
* \minus == \mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)
~~~

~~~ {.mycelium}
theorem minus-zero-l
* \minus(\zero)(a) == \if(\just(\zero))(\nothing)(\eq(\zero)(a))

proof
1. \minus(\zero)(a) : chain
    == \mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(\zero)(a) : use def-minus; at z in z(\zero)(a)
    == \comp(\if(\just(\zero))(\nothing))(\eq(\zero))(a) : use mutrec-zero;
    == \if(\just(\zero))(\nothing)(\eq(\zero)(a)) : use def-comp;
~~~

~~~ {.mycelium}
theorem minus-zero-next
* \minus(\zero)(\next(n)) == \nothing

proof
1. \minus(\zero)(\next(n)) : chain
    == \if(\just(\zero))(\nothing)(\eq(\zero)(\next(n))) : use minus-zero-l;
    == \if(\just(\zero))(\nothing)(\false) : use eq-zero-next; at z in \if(\just(\zero))(\nothing)(z)
    == \nothing : use if-false;
~~~

~~~ {.mycelium}
theorem minus-zero-r
* \minus(m)(\zero) == \just(m)

proof
1.    m == \zero : hypothesis zero
2.    \minus(m)(\zero) : chain
       == \minus(\zero)(\zero) : hypothesis zero at z in \minus(z)(\zero)
       == \if(\just(\zero))(\nothing)(\eq(\zero)(\zero)) : use minus-zero-l;
       == \if(\just(\zero))(\nothing)(\true) : use eq-refl; at z in \if(\just(\zero))(\nothing)(z)
       == \just(\zero) : use if-true;
       == \just(m) : flop hypothesis zero at z in \just(z)
3.  (m == \zero) => (\minus(m)(\zero) == \just(m)) : discharge zero; 2
4.    (m == n) => (\minus(m)(\zero) == \just(m)) : hypothesis n
5.    (n == n) => (\minus(n)(\zero) == \just(n)) : sub [m :-> n]; 4
6.    n == n : eq-intro
7.    \minus(n)(\zero) == \just(n) : use impl-elim; 6, 5
8.      m == \next(n) : hypothesis next
9.      \minus(m)(\zero) : chain
         == \minus(\next(n))(\zero) : hypothesis next at z in \minus(z)(\zero)
         == \mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(\next(n))(\zero) : use def-minus; at z in z(\next(n))(\zero)
         == \minusH(n)(\zero)(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(n)(\const(\comp(\opt(\zero)(\id))(\prev))(n)(\zero))) : use mutrec-next;
         == \minusH(n)(\zero)(\minus(n)(\const(\comp(\opt(\zero)(\id))(\prev))(n)(\zero))) : flop use def-minus; at z in \minusH(n)(\zero)(z(n)(\const(\comp(\opt(\zero)(\id))(\prev))(n)(\zero)))
         == \minusH(n)(\zero)(\minus(n)(\comp(\opt(\zero)(\id))(\prev)(\zero))) : use def-const; at z in \minusH(n)(\zero)(\minus(n)(z(\zero)))
         == \minusH(n)(\zero)(\minus(n)(\opt(\zero)(\id)(\prev(\zero)))) : use def-comp; at z in \minusH(n)(\zero)(\minus(n)(z))
         == \minusH(n)(\zero)(\minus(n)(\opt(\zero)(\id)(\nothing))) : use prev-zero; at z in \minusH(n)(\zero)(\minus(n)(\opt(\zero)(\id)(z)))
         == \minusH(n)(\zero)(\minus(n)(\zero)) : use opt-nothing; at z in \minusH(n)(\zero)(\minus(n)(z))
         == \minusH(n)(\zero)(\just(n)) : use reiterate; 7 at z in \minusH(n)(\zero)(z)
         == \if(\just(\next(n)))(\just(n))(\eq(\zero)(\zero)) : use def-minus-helper;
         == \if(\just(\next(n)))(\just(n))(\true) : use eq-refl; at z in \if(\just(\next(n)))(\just(n))(z)
         == \just(\next(n)) : use if-true;
         == \just(m) : flop hypothesis next at z in \just(z)
10.   (m == \next(n)) => (\minus(m)(\zero) == \just(m)) : discharge next; 9
11. ((m == n) => (\minus(m)(\zero) == \just(m))) =>
      ((m == \next(n)) => (\minus(m)(\zero) == \just(m))) : discharge n; 10
12. ∀k. ((m == k) => (\minus(m)(\zero) == \just(m))) =>
      ((m == \next(k)) => (\minus(m)(\zero) == \just(m))) : forall-intro n -> k; 11
13. \minus(m)(\zero) == \just(m) : use nat-induction; 3, 12
~~~

~~~ {.mycelium}
theorem minus-next-next
* \minus(\next(a))(\next(b)) == \minus(a)(b)

proof
1. \minus(\next(a))(\next(b)) : chain
    == \mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(\next(a))(\next(b)) : use def-minus; at z in z(\next(a))(\next(b))
    == \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(\const(\comp(\opt(\zero)(\id))(\prev))(a)(\next(b)))) : use mutrec-next;
    == \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(\comp(\opt(\zero)(\id))(\prev)(\next(b)))) : use def-const; at z in \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(z(\next(b))))
    == \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(\opt(\zero)(\id)(\prev(\next(b))))) : use def-comp; at z in \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(z))
== \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(\opt(\zero)(\id)(\comp(\prev)(\next)(b)))) : flop use def-comp; at z in \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(\opt(\zero)(\id)(z)))
    == \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(\opt(\zero)(\id)(\just(b)))) : use prev-next; at z in \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(\opt(\zero)(\id)(z(b))))
    == \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(\id(b))) : use opt-just; at z in \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(z))
    == \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(b)) : use def-id; at z in \minusH(a)(\next(b))(\mutrec(\comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(\const(\comp(\opt(\zero)(\id))(\prev)))(\minusH)(a)(z))
    == \minusH(a)(\next(b))(\minus(a)(b)) : flop use def-minus; at z in \minusH(a)(\next(b))(z(a)(b))
    == \if(\just(\next(a)))(\minus(a)(b))(\eq(\zero)(\next(b))) : use def-minus-helper;
    == \if(\just(\next(a)))(\minus(a)(b))(\false) : use eq-zero-next; at z in \if(\just(\next(a)))(\minus(a)(b))(z)
    == \minus(a)(b) : use if-false;
~~~

~~~ {.mycelium}
theorem minus-self-next
* \minus(m)(\next(m)) == \nothing

proof
1.    m == \zero : hypothesis zero
2.    \minus(m)(\next(m)) : chain
       == \minus(\zero)(\next(\zero)) : hypothesis zero at z in \minus(z)(\next(z))
       == \nothing : use minus-zero-next;
3.  (m == \zero) => (\minus(m)(\next(m)) == \nothing) : discharge zero; 2
4.    (m == n) => (\minus(m)(\next(m)) == \nothing) : hypothesis n
5.    (n == n) => (\minus(n)(\next(n)) == \nothing) : sub [m :-> n]; 4
6.    n == n : eq-intro
7.    \minus(n)(\next(n)) == \nothing : use impl-elim; 6, 5
8.      m == \next(n) : hypothesis next
9.      \minus(m)(\next(m)) : chain
         == \minus(\next(n))(\next(\next(n))) : hypothesis next at z in \minus(z)(\next(z))
         == \minus(n)(\next(n)) : use minus-next-next;
         == \nothing : use reiterate; 7
10.   (m == \next(n)) => (\minus(m)(\next(m)) == \nothing) : discharge next; 9
11. ((m == n) => (\minus(m)(\next(m)) == \nothing)) =>
      ((m == \next(n)) => (\minus(m)(\next(m)) == \nothing)) : discharge n; 10
12. ∀k. ((m == k) => (\minus(m)(\next(m)) == \nothing)) =>
      ((m == \next(k)) => (\minus(m)(\next(m)) == \nothing)) : forall-intro n -> k; 11
13. \minus(m)(\next(m)) == \nothing : use nat-induction; 3, 12
~~~
