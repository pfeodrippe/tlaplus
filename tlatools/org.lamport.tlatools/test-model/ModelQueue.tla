---- MODULE ModelQueue ----
EXTENDS Naturals

VARIABLE queue

Init == queue = 0

Next == queue' = IF queue < 2 THEN queue + 1 ELSE queue

\* Invariant: queue never exceeds 2
Inv == queue <= 2

====
