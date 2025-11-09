---- MODULE ModelCounter ----
EXTENDS Naturals

VARIABLE counter

Init == counter = 0

Next == counter' = IF counter < 5 THEN counter + 1 ELSE counter

\* Invariant: counter should not exceed 3
\* This will be violated when counter = 4
Inv == counter <= 3

====
