---- MODULE ModelB_RunFlag ----
EXTENDS Naturals, TLC, RunFlagModule

VARIABLE b

Init == b = 0

Next == b' = IF b < 3 THEN b + 1 ELSE b

\* Invariant that relies on the Java override. If the Java override reports that
\* the TLC globals are set, Inv is true and the model passes. If the override
\* reports false (i.e. globals were reset), Inv is violated.
Inv == CheckGlobalsSet

====
