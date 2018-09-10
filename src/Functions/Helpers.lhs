---
title: Helper Functions
---

~~~ {.mycelium}
type \thread :: (u -> b -> c) -> (u -> a -> b) -> u -> a -> c

definition def-thread
* \thread(g)(f)(u) == \comp(g(u))(f(u))
~~~

~~~ {.mycelium}
type \ap2 :: (a -> b -> c) -> (a -> b) -> a -> c

definition def-ap2
* \ap2(g)(f)(a) == g(a)(f(a))
~~~
