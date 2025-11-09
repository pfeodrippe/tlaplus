---- MODULE ModelB_Flag ----
EXTENDS Naturals, FlagSetterModule

VARIABLE y

Init == y = 0

Next == y' = IF y < 3 THEN y + 1 ELSE y

\* The invariant uses the Java-side GetFlag operator. 
\* If the flag was set (by ModelA in a prior run), GetFlag returns TRUE and invariant holds.
\* If the flag was not set, GetFlag returns FALSE and the invariant is violated.
Inv == GetFlag

====
