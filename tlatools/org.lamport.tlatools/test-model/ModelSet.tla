---- MODULE ModelSet ----
EXTENDS Naturals

VARIABLE set_size

Init == set_size = 0

Next == set_size' = IF set_size < 3 THEN set_size + 1 ELSE set_size

\* Invariant: set size never exceeds 3
Inv == set_size <= 3

====
