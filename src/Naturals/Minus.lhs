---
title: Minus
---

~~~ {.mycelium}
type \minusH :: Nat -> Nat -> Maybe Nat -> Maybe Nat

definition def-minus-helper
* \minusH(a)(b)(u)
   == \if(\just(\next(a)))(u)(\eq(\zero)(b))

type \minus :: Nat -> Nat -> Maybe Nat

definition def-minus
* \minus
   == \mutrec(
        \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
        \const(\comp(\opt(\zero)(\id))(\prev)))(
        \minusH)
~~~

~~~ {.mycelium}
theorem minus-zero-l
* \minus(\zero)(a) == \if(\just(\zero))(\nothing)(\eq(\zero)(a))

proof
1. \minus(\zero)(a) : chain

    == \mutrec(
         \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
         \const(\comp(\opt(\zero)(\id))(\prev)))(
         \minusH)(
         \zero)(
         a)
     : use def-minus; at z in z(\zero)(a)

    == \comp(\if(\just(\zero))(\nothing))(\eq(\zero))(a)
     : use mutrec-zero;

    == \if(\just(\zero))(\nothing)(\eq(\zero)(a))
     : use def-comp;
~~~

~~~ {.mycelium}
theorem minus-zero-next
* \minus(\zero)(\next(n)) == \nothing

proof
1. \minus(\zero)(\next(n)) : chain

    == \if(\just(\zero))(\nothing)(\eq(\zero)(\next(n)))
     : use minus-zero-l;

    == \if(\just(\zero))(\nothing)(\false)
     : use eq-zero-next; at z in
       \if(\just(\zero))(\nothing)(z)

    == \nothing
     : use if-false;
~~~

~~~ {.mycelium}
theorem minus-zero-r
* \minus(m)(\zero) == \just(m)

proof
1.  \minus(\zero)(\zero) : chain

     == \if(\just(\zero))(\nothing)(\eq(\zero)(\zero))
      : use minus-zero-l;

     == \if(\just(\zero))(\nothing)(\true)
      : use eq-refl; at z in
        \if(\just(\zero))(\nothing)(z)

     == \just(\zero)
      : use if-true;

2.    \minus(n)(\zero) == \just(n) : hypothesis n

3.    \minus(\next(n))(\zero) : chain

       == \mutrec(
            \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
            \const(\comp(\opt(\zero)(\id))(\prev)))(
            \minusH)(
            \next(n))(
            \zero)
        : use def-minus; at z in z(\next(n))(\zero)

       == \minusH(n)(\zero)(
            \mutrec(
              \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
              \const(\comp(\opt(\zero)(\id))(\prev)))(
              \minusH)(
              n)(
              \const(\comp(\opt(\zero)(\id))(\prev))(n)(\zero)))
        : use mutrec-next;

       == \minusH(n)(\zero)(
            \minus(n)(
              \const(\comp(\opt(\zero)(\id))(\prev))(n)(\zero)))
        : flop use def-minus; at z in
          \minusH(n)(\zero)(
            z(n)(
              \const(\comp(\opt(\zero)(\id))(\prev))(n)(\zero)))

       == \minusH(n)(\zero)(
            \minus(n)(\comp(\opt(\zero)(\id))(\prev)(\zero)))
        : use def-const; at z in
          \minusH(n)(\zero)(
            \minus(n)(z(\zero)))

       == \minusH(n)(\zero)(
            \minus(n)(\opt(\zero)(\id)(\prev(\zero))))
        : use def-comp; at z in
          \minusH(n)(\zero)(
            \minus(n)(z))

       == \minusH(n)(\zero)(
            \minus(n)(\opt(\zero)(\id)(\nothing)))
        : use prev-zero; at z in
          \minusH(n)(\zero)(
            \minus(n)(\opt(\zero)(\id)(z)))

       == \minusH(n)(\zero)(\minus(n)(\zero))
        : use opt-nothing; at z in
          \minusH(n)(\zero)(\minus(n)(z))

       == \minusH(n)(\zero)(\just(n))
        : hypothesis n at z in
          \minusH(n)(\zero)(z)

       == \if(\just(\next(n)))(\just(n))(\eq(\zero)(\zero))
        : use def-minus-helper;

       == \if(\just(\next(n)))(\just(n))(\true)
        : use eq-refl; at z in
          \if(\just(\next(n)))(\just(n))(z)

       == \just(\next(n))
        : use if-true;

4.  (\minus(n)(\zero) == \just(n)) =>
      (\minus(\next(n))(\zero) == \just(\next(n)))
     : discharge n; 3

5.  ∀k. (\minus(k)(\zero) == \just(k)) =>
      (\minus(\next(k))(\zero) == \just(\next(k)))
     : forall-intro n -> k; 4

6.  ∀k. \minus(k)(\zero) == \just(k)
     : invoke nat-induction
       [P :-> \minus(_)(\zero) == \just(_)]; 1, 5

7.  \minus(m)(\zero) == \just(m)
     : forall-elim k -> m; 6
~~~

~~~ {.mycelium}
theorem minus-next-next
* \minus(\next(a))(\next(b)) == \minus(a)(b)

proof
1. \minus(\next(a))(\next(b)) : chain

    == \mutrec(
         \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
         \const(\comp(\opt(\zero)(\id))(\prev)))(
         \minusH)(
         \next(a))(
         \next(b))
     : use def-minus; at z in z(\next(a))(\next(b))

    == \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           \const(\comp(\opt(\zero)(\id))(\prev))(a)(\next(b))))
     : use mutrec-next;

    == \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           \comp(\opt(\zero)(\id))(\prev)(\next(b))))
     : use def-const; at z in
       \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           z(\next(b))))

    == \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           \opt(\zero)(\id)(\prev(\next(b)))))
     : use def-comp; at z in
       \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           z))

    == \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           \opt(\zero)(\id)(\comp(\prev)(\next)(b))))
     : flop use def-comp; at z in
       \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           \opt(\zero)(\id)(z)))

    == \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           \opt(\zero)(\id)(\just(b))))
     : use prev-next; at z in
       \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           \opt(\zero)(\id)(z(b))))

    == \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           \id(b)))
     : use opt-just; at z in
       \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           z))

    == \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           b))
     : use def-id; at z in
       \minusH(a)(\next(b))(
         \mutrec(
           \comp(\if(\just(\zero))(\nothing))(\eq(\zero)))(
           \const(\comp(\opt(\zero)(\id))(\prev)))(
           \minusH)(
           a)(
           z))

    == \minusH(a)(\next(b))(\minus(a)(b))
     : flop use def-minus; at z in
       \minusH(a)(\next(b))(z(a)(b))

    == \if(\just(\next(a)))(\minus(a)(b))(\eq(\zero)(\next(b)))
     : use def-minus-helper;

    == \if(\just(\next(a)))(\minus(a)(b))(\false)
     : use eq-zero-next; at z in
       \if(\just(\next(a)))(\minus(a)(b))(z)

    == \minus(a)(b)
     : use if-false;
~~~

~~~ {.mycelium}
theorem minus-self-next
* \minus(m)(\next(m)) == \nothing

proof
1. \minus(\zero)(\next(\zero)) == \nothing
    : use minus-zero-next;

2.   \minus(n)(\next(n)) == \nothing
      : hypothesis n

3.   \minus(\next(n))(\next(\next(n))) : chain
      == \minus(n)(\next(n)) : use minus-next-next;
      == \nothing : hypothesis n

4. (\minus(n)(\next(n)) == \nothing) =>
     (\minus(\next(n))(\next(\next(n))) == \nothing)
    : discharge n; 3

5. ∀k. (\minus(k)(\next(k)) == \nothing) =>
     (\minus(\next(k))(\next(\next(k))) == \nothing)
    : forall-intro n -> k; 4

6. ∀k. \minus(k)(\next(k)) == \nothing
    : invoke nat-induction
      [P :-> \minus(_)(\next(_)) == \nothing]; 1, 5

7. \minus(m)(\next(m)) == \nothing
    : forall-elim k -> m; 6
~~~

~~~ {.mycelium}
theorem minus-self
* \minus(a)(a) == \just(\zero)

proof
1. \minus(\zero)(\zero) : chain
    == \if(\just(\zero))(\nothing)(\eq(\zero)(\zero))
     : use minus-zero-l;
    == \if(\just(\zero))(\nothing)(\true)
     : use eq-refl; at z in
       \if(\just(\zero))(\nothing)(z)
    == \just(\zero)
     : use if-true;

2.   \minus(n)(n) == \just(\zero)
      : hypothesis n

3.   \minus(\next(n))(\next(n)) : chain
      == \minus(n)(n) : use minus-next-next;
      == \just(\zero) : hypothesis n

4. (\minus(n)(n) == \just(\zero)) =>
     (\minus(\next(n))(\next(n)) == \just(\zero))
    : discharge n; 3

5. ∀k. (\minus(k)(k) == \just(\zero)) =>
     (\minus(\next(k))(\next(k)) == \just(\zero))
    : forall-intro n -> k; 4

6. ∀k. \minus(k)(k) == \just(\zero)
    : invoke nat-induction
      [P :-> \minus(_)(_) == \just(\zero)]; 1, 5

7. \minus(a)(a) == \just(\zero)
    : forall-elim k -> a; 6
~~~

~~~ {.mycelium}
theorem minus-is-zero
if
  * \minus(a)(b) == \just(\zero)
then
  * a == b

proof
1.    \minus(a)(\zero) == \just(\zero) : hypothesis zero

2.    \just(a) : chain
       == \minus(a)(\zero) : flop use minus-zero-r;
       == \just(\zero) : hypothesis zero

3.    a == \zero : use just-inj; 2

4.  (\minus(a)(\zero) == \just(\zero)) => (a == \zero)
     : discharge zero; 3

5.  ∀k. (\minus(k)(\zero) == \just(\zero)) => (k == \zero)
     : forall-intro a -> k; 4

6.    ∀k. (\minus(k)(n) == \just(\zero)) => (k == n) : hypothesis n

7.      \minus(a)(\next(n)) == \just(\zero) : hypothesis next

8.        a == \zero : hypothesis a-zero

9.        \nothing : chain
           == \minus(\zero)(\next(n))
            : flop use minus-zero-next;
           == \minus(a)(\next(n))
            : flop hypothesis a-zero at z in \minus(z)(\next(n))
           == \just(\zero)
            : hypothesis next

10.       ∃k. \nothing == \just(k)
           : exists-intro k <- \zero; 9

11.     (a == \zero) => (∃k. \nothing == \just(k))
         : discharge a-zero; 10

12.     ~(∃k. \nothing == \just(k)) : use maybe-disc;

13.     ~(a == \zero) : use modus-tollens; 11, 12

14.     (a == \zero) \/ (∃k. a == \next(k)) : use nat-disj-cases-1;

15.     ∃k. a == \next(k) : use disj-syllogism-l; 14, 13

16.       a == \next(u) : hypothesis a-u

17.       \minus(u)(n) : chain
           == \minus(\next(u))(\next(n))
            : flop use minus-next-next;
           == \minus(a)(\next(n))
            : flop hypothesis a-u at z in
              \minus(z)(\next(n))
           == \just(\zero)
            : hypothesis next

18.       (\minus(u)(n) == \just(\zero)) => (u == n)
           : forall-elim k -> u; 6

19.       u == n : use impl-elim; 17, 18

20.       a : chain
           == \next(u) : hypothesis a-u
           == \next(n) : use reiterate; 19 at z in \next(z)

21.     (a == \next(u)) => (a == \next(n)) : discharge a-u; 20

22.     a == \next(n) : exists-elim u <- k; 15, 21

23.   (\minus(a)(\next(n)) == \just(\zero)) =>
        (a == \next(n))
       : discharge next; 22

24.   ∀k. (\minus(k)(\next(n)) == \just(\zero)) =>
        (k == \next(n))
       : forall-intro a -> k; 23

25. (∀k. (\minus(k)(n) == \just(\zero)) => (k == n)) =>
      (∀k. (\minus(k)(\next(n)) == \just(\zero)) => (k == \next(n)))
     : discharge n; 24

26. ∀u. (∀k. (\minus(k)(u) == \just(\zero)) => (k == u)) =>
      (∀k. (\minus(k)(\next(u)) == \just(\zero)) => (k == \next(u)))
     : forall-intro n -> u; 25

27. ∀u. (∀k. (\minus(k)(u) == \just(\zero)) => (k == u))
     : invoke nat-induction
       [P :-> ∀k. (\minus(k)(_) == \just(\zero)) => (k == _)]; 5, 26

28. ∀k. (\minus(k)(b) == \just(\zero)) => (k == b)
     : forall-elim u -> b; 27

29. (\minus(a)(b) == \just(\zero)) => (a == b)
     : forall-elim k -> a; 28

30. \minus(a)(b) == \just(\zero) : assumption 1

31. a == b : use impl-elim; 30, 29
~~~

We can turn an equation with minus into an equation with plus:

~~~ {.mycelium}
theorem minus-to-plus
if
  * \minus(b)(a) == \just(c)
then
  * b == \plus(c)(a)

proof
1.    \minus(b)(\zero) == \just(c) : hypothesis zero

2.    \just(b) : chain
       == \minus(b)(\zero) : flop use minus-zero-r;
       == \just(c) : hypothesis zero

3.    b : chain
       == c : use just-inj; 2
       == \plus(c)(\zero) : flop use plus-zero-r;

4.  (\minus(b)(\zero) == \just(c)) => (b == \plus(c)(\zero))
     : discharge zero; 3

5.  ∀k. (\minus(k)(\zero) == \just(c)) => (k == \plus(c)(\zero))
     : forall-intro b -> k; 4

6.    ∀k. (\minus(k)(n) == \just(c)) => (k == \plus(c)(n))
       : hypothesis n

7.      \minus(b)(\next(n)) == \just(c) : hypothesis next

8.        b == \zero : hypothesis b-zero

9.        \nothing : chain
           == \minus(\zero)(\next(n))
            : flop use minus-zero-next;
           == \minus(b)(\next(n))
            : flop hypothesis b-zero at z in
              \minus(z)(\next(n))
           == \just(c)
            : hypothesis next

10.       ∃u. \nothing == \just(u) : exists-intro u <- c; 9

11.     (b == \zero) => (∃u. \nothing == \just(u))
         : discharge b-zero; 10

12.     ~(∃u. \nothing == \just(u)) : use maybe-disc;

13.     ~(b == \zero) : use modus-tollens; 11, 12

14.     (b == \zero) \/ (∃k. b == \next(k))
         : use nat-disj-cases-1;

15.     ∃k. b == \next(k)
         : use disj-syllogism-l; 14, 13

16.       b == \next(u) : hypothesis b-next-u

17.       (\minus(u)(n) == \just(c)) => (u == \plus(c)(n))
           : forall-elim k -> u; 6

18.       \minus(u)(n) : chain
           == \minus(\next(u))(\next(n))
            : flop use minus-next-next;
           == \minus(b)(\next(n))
            : flop hypothesis b-next-u at z in
              \minus(z)(\next(n))
           == \just(c)
            : hypothesis next

19.       u == \plus(c)(n) : use impl-elim; 18, 17

20.       b : chain
           == \next(u)
            : hypothesis b-next-u
           == \next(\plus(c)(n))
            : use reiterate; 19 at z in \next(z)
           == \plus(c)(\next(n))
            : flop use plus-next-r;

21.     (b == \next(u)) => (b == \plus(c)(\next(n)))
         : discharge b-next-u; 20

22.     b == \plus(c)(\next(n))
         : exists-elim u <- k; 15, 21

23.   (\minus(b)(\next(n)) == \just(c)) => (b == \plus(c)(\next(n)))
       : discharge next; 22

24.   ∀k. (\minus(k)(\next(n)) == \just(c)) =>
       (k == \plus(c)(\next(n)))
       : forall-intro b -> k; 23

25. (∀k. (\minus(k)(n) == \just(c)) =>
           (k == \plus(c)(n))) =>
      (∀k. (\minus(k)(\next(n)) == \just(c)) =>
        (k == \plus(c)(\next(n))))
     : discharge n; 24

26. ∀u. (∀k. (\minus(k)(u) == \just(c)) =>
          (k == \plus(c)(u))) =>
      (∀k. (\minus(k)(\next(u)) == \just(c)) =>
        (k == \plus(c)(\next(u))))
     : forall-intro n -> u; 25

27. ∀u. (∀k. (\minus(k)(u) == \just(c)) => (k == \plus(c)(u)))
     : invoke nat-induction
       [P :-> ∀k. (\minus(k)(_) == \just(c)) =>
               (k == \plus(c)(_))]; 5, 26

28. ∀k. (\minus(k)(a) == \just(c)) => (k == \plus(c)(a))
     : forall-elim u -> a; 27

29. (\minus(b)(a) == \just(c)) => (b == \plus(c)(a))
     : forall-elim k -> b; 28

30. \minus(b)(a) == \just(c) : assumption 1

31. b == \plus(c)(a) : use impl-elim; 30, 29
~~~

~~~ {.mycelium}
theorem minus-next-intro-l
if
  * \minus(a)(b) == \just(c)
then
  * \minus(\next(a))(b) == \just(\next(c))

proof
1.    \minus(a)(\zero) == \just(c) : hypothesis zero

2.    \just(a) : chain
       == \minus(a)(\zero) : flop use minus-zero-r;
       == \just(c) : hypothesis zero

3.    a == c : use just-inj; 2

4.    \minus(\next(a))(\zero) : chain
       == \just(\next(a))
        : use minus-zero-r;
       == \just(\next(c))
        : use reiterate; 3 at z in \just(\next(z))

5.  (\minus(a)(\zero) == \just(c)) =>
      (\minus(\next(a))(\zero) == \just(\next(c)))
     : discharge zero; 4

6.  ∀k. (\minus(k)(\zero) == \just(c)) =>
      (\minus(\next(k))(\zero) == \just(\next(c)))
     : forall-intro a -> k; 5

7.    ∀k. (\minus(k)(n) == \just(c)) =>
        (\minus(\next(k))(n) == \just(\next(c)))
       : hypothesis n

8.      \minus(a)(\next(n)) == \just(c)
         : hypothesis next

9.        a == \zero : hypothesis a-zero

10.       \nothing : chain
           == \minus(\zero)(\next(n))
            : flop use minus-zero-next;
           == \minus(a)(\next(n))
            : flop hypothesis a-zero at z in
              \minus(z)(\next(n))
           == \just(c)
            : hypothesis next

11.         ∃u. \nothing == \just(u)
             : exists-intro u <- c; 10

12.       (a == \zero) => (∃u. \nothing == \just(u))
           : discharge a-zero; 11

13.       ~(∃u. \nothing == \just(u)) : use maybe-disc;

14.       ~(a == \zero) : use modus-tollens; 12, 13

15.       (a == \zero) \/ (∃u. a == \next(u))
           : use nat-disj-cases-1;

16.       ∃u. a == \next(u) : use disj-syllogism-l; 15, 14

17.         a == \next(t) : hypothesis a-next-t

18.         \minus(t)(n) : chain
             == \minus(\next(t))(\next(n))
              : flop use minus-next-next;
             == \minus(a)(\next(n))
              : flop hypothesis a-next-t at z in
                \minus(z)(\next(n))
             == \just(c) : hypothesis next

19.         (\minus(t)(n) == \just(c)) => (\minus(\next(t))(n) == \just(\next(c)))
             : forall-elim k -> t; 7

20.         \minus(\next(t))(n) == \just(\next(c)) : use impl-elim; 18, 19

21.         \minus(\next(a))(\next(n)) : chain
             == \minus(a)(n)
              : use minus-next-next;
             == \minus(\next(t))(n)
              : hypothesis a-next-t at z in
                \minus(z)(n)
             == \just(\next(c))
              : use reiterate; 20

22.       (a == \next(t)) =>
            (\minus(\next(a))(\next(n)) == \just(\next(c)))
           : discharge a-next-t; 21

23.       \minus(\next(a))(\next(n)) == \just(\next(c))
           : exists-elim t <- u; 16, 22

24.     (\minus(a)(\next(n)) == \just(c)) =>
          (\minus(\next(a))(\next(n)) == \just(\next(c)))
         : discharge next; 23

25.     ∀k. (\minus(k)(\next(n)) == \just(c)) =>
          (\minus(\next(k))(\next(n)) == \just(\next(c)))
         : forall-intro a -> k; 24

26. (∀k. (\minus(k)(n) == \just(c)) =>
      (\minus(\next(k))(n) == \just(\next(c)))) =>
      (∀k. (\minus(k)(\next(n)) == \just(c)) =>
          (\minus(\next(k))(\next(n)) == \just(\next(c))))
     : discharge n; 25

27. ∀u. (∀k. (\minus(k)(u) == \just(c)) =>
      (\minus(\next(k))(u) == \just(\next(c)))) =>
      (∀k. (\minus(k)(\next(u)) == \just(c)) =>
          (\minus(\next(k))(\next(u)) == \just(\next(c))))
     : forall-intro n -> u; 26

28. ∀u. (∀k. (\minus(k)(u) == \just(c)) =>
      (\minus(\next(k))(u) == \just(\next(c))))
     : invoke nat-induction
       [P :-> (∀k. (\minus(k)(_) == \just(c)) =>
                (\minus(\next(k))(_) == \just(\next(c))))]; 6, 27

29. (∀k. (\minus(k)(b) == \just(c)) =>
      (\minus(\next(k))(b) == \just(\next(c))))
     : forall-elim u -> b; 28

30. (\minus(a)(b) == \just(c)) =>
      (\minus(\next(a))(b) == \just(\next(c)))
     : forall-elim k -> a; 29

31. \minus(a)(b) == \just(c) : assumption 1

32. \minus(\next(a))(b) == \just(\next(c)) : use impl-elim; 31, 30
~~~

~~~ {.mycelium}
theorem plus-to-minus
if
  * b == \plus(c)(a)
then
  * \minus(b)(a) == \just(c)

proof
1.    b == \plus(\zero)(a) : hypothesis zero

2.    \minus(b)(a) : chain
       == \minus(\plus(\zero)(a))(a)
        : hypothesis zero at z in \minus(z)(a)
       == \minus(a)(a)
        : use plus-zero-l; at z in \minus(z)(a)
       == \just(\zero)
        : use minus-self;

3.  (b == \plus(\zero)(a)) =>
      (\minus(b)(a) == \just(\zero))
     : discharge zero; 2

4.  ∀k. (k == \plus(\zero)(a)) =>
      (\minus(k)(a) == \just(\zero))
     : forall-intro b -> k; 3

5.    ∀k. (k == \plus(n)(a)) => (\minus(k)(a) == \just(n))
       : hypothesis n

6.      b == \plus(\next(n))(a)
         : hypothesis next

7.        b == \zero : hypothesis b-zero

8.        \zero : chain
           == b : flop hypothesis b-zero
           == \plus(\next(n))(a) : hypothesis next
           == \next(\plus(n)(a)) : use plus-next-l;

9.        ∃u. \zero == \next(u)
           : exists-intro u <- \plus(n)(a); 8

10.     (b == \zero) => (∃u. \zero == \next(u))
         : discharge b-zero; 9

11.     ~(∃u. \zero == \next(u)) : use nat-disc;

12.     ~(b == \zero) : use modus-tollens; 10, 11

13.     (b == \zero) \/ (∃u. b == \next(u))
         : use nat-disj-cases-1;

14.     ∃u. b == \next(u)
         : use disj-syllogism-l; 13, 12

15.       b == \next(t) : hypothesis b-next-t

16.       (t == \plus(n)(a)) => (\minus(t)(a) == \just(n))
           : forall-elim k -> t; 5

17.       \next(t) : chain
           == b : flop hypothesis b-next-t
           == \plus(\next(n))(a) : hypothesis next
           == \next(\plus(n)(a)) : use plus-next-l;

18.       t == \plus(n)(a) : use next-inj; 17

19.       \minus(t)(a) == \just(n) : use impl-elim; 18, 16

20.       \minus(\next(t))(a) == \just(\next(n))
           : use minus-next-intro-l; 19

21.       \minus(b)(a) : chain
           == \minus(\next(t))(a)
            : hypothesis b-next-t at z in
              \minus(z)(a)
           == \just(\next(n))
            : use reiterate; 20

22.     (b == \next(t)) => (\minus(b)(a) == \just(\next(n)))
         : discharge b-next-t; 21

23.     \minus(b)(a) == \just(\next(n)) : exists-elim t <- u; 14, 22

24.   (b == \plus(\next(n))(a)) => (\minus(b)(a) == \just(\next(n)))
       : discharge next; 23

25.   ∀k. (k == \plus(\next(n))(a)) => (\minus(k)(a) == \just(\next(n)))
       : forall-intro b -> k; 24

26. (∀k. (k == \plus(n)(a)) =>
           (\minus(k)(a) == \just(n))) =>
      (∀k. (k == \plus(\next(n))(a)) =>
        (\minus(k)(a) == \just(\next(n))))
     : discharge n; 25

27. ∀u. (∀k. (k == \plus(u)(a)) =>
          (\minus(k)(a) == \just(u))) =>
      (∀k. (k == \plus(\next(u))(a)) =>
        (\minus(k)(a) == \just(\next(u))))
     : forall-intro n -> u; 26

28. ∀u. (∀k. (k == \plus(u)(a)) =>
          (\minus(k)(a) == \just(u)))
     : invoke nat-induction
       [P :-> ∀k. (k == \plus(_)(a)) =>
               (\minus(k)(a) == \just(_))]; 4, 27

29. ∀k. (k == \plus(c)(a)) => (\minus(k)(a) == \just(c))
     : forall-elim u -> c; 28

30. (b == \plus(c)(a)) => (\minus(b)(a) == \just(c))
     : forall-elim k -> b; 29

31. b == \plus(c)(a) : assumption 1

32. \minus(b)(a) == \just(c) : use impl-elim; 31, 30
~~~

~~~ {.mycelium}
theorem minus-next-cancel-l
if
  * \minus(\next(a))(b) == \just(\next(c))
then
  * \minus(a)(b) == \just(c)

proof
1. \minus(\next(a))(b) == \just(\next(c)) : assumption 1
2. \next(a) : chain
    == \plus(\next(c))(b) : use minus-to-plus; 1
    == \next(\plus(c)(b)) : use plus-next-l;
3. a == \plus(c)(b) : use next-inj; 2
4. \minus(a)(b) == \just(c) : use plus-to-minus; 3
~~~

~~~ {.mycelium}
theorem minus-cancel-r
if
  * \minus(a)(c) == \just(d)
  * \minus(b)(c) == \just(d)
then
  * a == b

proof
1. \minus(a)(c) == \just(d) : assumption 1
2. a == \plus(d)(c) : use minus-to-plus; 1
3. \minus(b)(c) == \just(d) : assumption 2
4. b == \plus(d)(c) : use minus-to-plus; 3
5. a : chain
    == \plus(d)(c) : use reiterate; 2
    == b : flop use reiterate; 4
~~~

~~~ {.mycelium}
theorem minus-cancel-l
if
  * \minus(c)(a) == \just(d)
  * \minus(c)(b) == \just(d)
then
  * a == b

proof
1. \minus(c)(a) == \just(d) : assumption 1
2. c == \plus(d)(a) : use minus-to-plus; 1
3. \minus(c)(b) == \just(d) : assumption 2
4. c == \plus(d)(b) : use minus-to-plus; 3
5. \plus(d)(a) : chain
    == c : flop use reiterate; 2
    == \plus(d)(b) : use reiterate; 4
6. a == b : use plus-cancel-l; 5
~~~

~~~ {.mycelium}
theorem minus-plus-inverse-r
* \minus(\plus(a)(b))(b) == \just(a)

proof
1. \plus(a)(b) == \plus(a)(b) : eq-intro
2. \minus(\plus(a)(b))(b) == \just(a) : use plus-to-minus; 1
~~~

~~~ {.mycelium}
theorem minus-plus-inverse-l
* \minus(\plus(b)(a))(b) == \just(a)

proof
1. \plus(b)(a) == \plus(a)(b) : use plus-comm;
2. \minus(\plus(b)(a))(b) == \just(a) : use plus-to-minus; 1
~~~

~~~ {.mycelium}
theorem minus-swap
if
  * \minus(c)(a) == \just(b)
then
  * \minus(c)(b) == \just(a)

proof
1. \minus(c)(a) == \just(b) : assumption 1
2. c : chain
    == \plus(b)(a) : use minus-to-plus; 1
    == \plus(a)(b) : use plus-comm;
3. \minus(c)(b) == \just(a) : use plus-to-minus; 2
~~~

~~~ {.mycelium}
theorem minus-flip
if
  * \minus(a)(b) == \nothing
then
  * ∃c. \minus(b)(a) == \just(\next(c))

proof
1.    \minus(\zero)(b) == \nothing : hypothesis zero

2.      b == \zero : hypothesis b-zero

3.      \nothing : chain
         == \minus(\zero)(b)
          : flop hypothesis zero
         == \minus(\zero)(\zero)
          : hypothesis b-zero at z in
            \minus(\zero)(z)
         == \just(\zero)
          : use minus-zero-r;

4.      ∃u. \nothing == \just(u)
         : exists-intro u <- \zero; 3

5.    (b == \zero) => (∃u. \nothing == \just(u))
       : discharge b-zero; 4

6.    ~(∃u. \nothing == \just(u)) : use maybe-disc;

7.    ~(b == \zero) : use modus-tollens; 5, 6

8.    (b == \zero) \/ (∃u. b == \next(u))
       : use nat-disj-cases-1;

9.    ∃u. b == \next(u) : use disj-syllogism-l; 8, 7

10.     b == \next(t) : hypothesis b-next-t

11.     \minus(b)(\zero) : chain
         == \just(b)
          : use minus-zero-r;
         == \just(\next(t))
          : hypothesis b-next-t at z in
            \just(z)

12.     ∃u. \minus(b)(\zero) == \just(\next(u))
         : exists-intro u <- t; 11

13.   (b == \next(t)) =>
        (∃u. \minus(b)(\zero) == \just(\next(u)))
       : discharge b-next-t; 12

14.   ∃u. \minus(b)(\zero) == \just(\next(u))
       : exists-elim t <- u; 9, 13

15. (\minus(\zero)(b) == \nothing) =>
      (∃u. \minus(b)(\zero) == \just(\next(u)))
     : discharge zero; 14

16. ∀k. (\minus(\zero)(k) == \nothing) =>
      (∃u. \minus(k)(\zero) == \just(\next(u)))
     : forall-intro b -> k; 15

17.   ∀k. (\minus(n)(k) == \nothing) =>
        (∃u. \minus(k)(n) == \just(\next(u)))
       : hypothesis n

18.     \minus(\next(n))(b) == \nothing
         : hypothesis next

19.       b == \zero : hypothesis b-zero

20.       \nothing : chain
           == \minus(\next(n))(b)
            : flop hypothesis next
           == \minus(\next(n))(\zero)
            : hypothesis b-zero at z in
              \minus(\next(n))(z)
           == \just(\next(n))
            : use minus-zero-r;

21.       ∃u. \nothing == \just(u)
           : exists-intro u <- \next(n); 20

22.     (b == \zero) => (∃u. \nothing == \just(u))
         : discharge b-zero; 21

23.     ~(∃u. \nothing == \just(u)) : use maybe-disc;

24.     ~(b == \zero) : use modus-tollens; 22, 23

25.     (b == \zero) \/ (∃u. b == \next(u)) : use nat-disj-cases-1;

26.     ∃u. b == \next(u) : use disj-syllogism-l; 25, 24

27.       b == \next(t) : hypothesis b-next-t

28.       (\minus(n)(t) == \nothing) =>
            (∃u. \minus(t)(n) == \just(\next(u)))
           : forall-elim k -> t; 17

29.       \minus(n)(t) : chain
           == \minus(\next(n))(\next(t))
            : flop use minus-next-next;
           == \minus(\next(n))(b)
            : flop hypothesis b-next-t at z in
              \minus(\next(n))(z)
           == \nothing
            : hypothesis next

30.       ∃u. \minus(t)(n) == \just(\next(u))
           : use impl-elim; 29, 28

31.         \minus(t)(n) == \just(\next(s))
             : hypothesis minus-just-next

32.         \minus(b)(\next(n)) : chain
             == \minus(\next(t))(\next(n))
              : hypothesis b-next-t at z in
                \minus(z)(\next(n))
             == \minus(t)(n)
              : use minus-next-next;
             == \just(\next(s))
              : hypothesis minus-just-next

33.         ∃u. \minus(b)(\next(n)) == \just(\next(u))
             : exists-intro u <- s; 32

34.       (\minus(t)(n) == \just(\next(s))) =>
            (∃u. \minus(b)(\next(n)) == \just(\next(u)))
           : discharge minus-just-next; 33

35.       ∃u. \minus(b)(\next(n)) == \just(\next(u))
           : exists-elim s <- u; 30, 34

36.     (b == \next(t)) =>
          (∃u. \minus(b)(\next(n)) == \just(\next(u)))
         : discharge b-next-t; 35

37.     ∃u. \minus(b)(\next(n)) == \just(\next(u))
         : exists-elim t <- u; 26, 36

38.   (\minus(\next(n))(b) == \nothing) =>
        (∃u. \minus(b)(\next(n)) == \just(\next(u)))
       : discharge next; 37

39.   ∀k. (\minus(\next(n))(k) == \nothing) =>
        (∃u. \minus(k)(\next(n)) == \just(\next(u)))
       : forall-intro b -> k; 38

40. (∀k. (\minus(n)(k) == \nothing) =>
        (∃u. \minus(k)(n) == \just(\next(u)))) =>
      (∀k. (\minus(\next(n))(k) == \nothing) =>
        (∃u. \minus(k)(\next(n)) == \just(\next(u))))
     : discharge n; 39

41. ∀h. (∀k. (\minus(h)(k) == \nothing) =>
        (∃u. \minus(k)(h) == \just(\next(u)))) =>
      (∀k. (\minus(\next(h))(k) == \nothing) =>
        (∃u. \minus(k)(\next(h)) == \just(\next(u))))
     : forall-intro n -> h; 40

42. ∀h. (∀k. (\minus(h)(k) == \nothing) =>
      (∃u. \minus(k)(h) == \just(\next(u))))
     : invoke nat-induction
       [P :-> (∀k. (\minus(_)(k) == \nothing) =>
                (∃u. \minus(k)(_) == \just(\next(u))))]; 16, 41

43. (∀k. (\minus(a)(k) == \nothing) =>
      (∃u. \minus(k)(a) == \just(\next(u))))
     : forall-elim h -> a; 42

44. (\minus(a)(b) == \nothing) =>
      (∃u. \minus(b)(a) == \just(\next(u)))
     : forall-elim k -> b; 43

45. \minus(a)(b) == \nothing : assumption 1

46. ∃u. \minus(b)(a) == \just(\next(u))
     : use impl-elim; 45, 44
~~~

~~~ {.mycelium}
theorem times-minus-dist-l
if
  * \minus(a)(b) == \just(d)
then
  * \minus(\times(c)(a))(\times(c)(b)) == \just(\times(c)(d))

proof
1. \minus(a)(b) == \just(d) : assumption 1
2. a == \plus(d)(b) : use minus-to-plus; 1
3. \times(c)(a) : chain
    == \times(c)(\plus(d)(b))
     : use reiterate; 2 at z in \times(c)(z)
    == \plus(\times(c)(d))(\times(c)(b))
     : use times-plus-dist-l;
4. \minus(\times(c)(a))(\times(c)(b)) == \just(\times(c)(d))
    : use plus-to-minus; 3
~~~
