---- MODULE ModelB ----
EXTENDS Naturals

VARIABLE b

Init == b = 0

Next == b' = IF b < 3 THEN b + 1 ELSE b

Inv == b < 3

====
