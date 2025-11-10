---- MODULE ModelWithOverride1 ----
EXTENDS Naturals

(* This model uses a custom operator MyAdd *)
VARIABLE counter

MyAdd(a, b) == a + b + 10  \* Implementation: adds 10 to the result

Init == counter = 0

Next == counter' = MyAdd(counter, 1)

Inv == counter <= 100

====
