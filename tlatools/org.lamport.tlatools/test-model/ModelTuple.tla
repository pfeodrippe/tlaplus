---- MODULE ModelTuple ----
EXTENDS Naturals

VARIABLE value

Init == value = 1

Next == value' = IF value < 4 THEN value + 1 ELSE value

\* Invariant: value never exceeds 4
Inv == value <= 4

====
