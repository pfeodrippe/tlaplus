---- MODULE ModelA_Flag ----
EXTENDS Naturals, FlagSetterModule

VARIABLE x

\* Init: call SetFlag to set the persistent Java flag, then initialize x
Init == SetFlag /\ x = 0

\* Next: simple increment
Next == x' = IF x < 2 THEN x + 1 ELSE x

\* Invariant: just check that x is within bounds (should always hold)
Inv == x <= 3

====
