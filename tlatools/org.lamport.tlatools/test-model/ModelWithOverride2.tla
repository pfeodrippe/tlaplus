---- MODULE ModelWithOverride2 ----
EXTENDS Naturals

(* This model uses a custom operator MyAdd with different implementation *)
VARIABLE counter

MyAdd(a, b) == a + b + 20  \* Different implementation: adds 20 to the result

Init == counter = 0

Next == counter' = MyAdd(counter, 1)

Inv == counter <= 100

====
