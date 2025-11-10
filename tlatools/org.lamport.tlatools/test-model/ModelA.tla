---- MODULE ModelA ----
EXTENDS Naturals

VARIABLE a

Init == a = 0

Next == a' = IF a < 2 THEN a + 1 ELSE a

Inv == a < 2

====
