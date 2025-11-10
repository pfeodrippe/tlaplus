---- MODULE DynamicSpec ----
EXTENDS Integers
VARIABLES x
TheOp == 4 + 4
Init == x = 0
Action == /\ x < 10 /\ x' = x + 1
Next == Action \/ (x = 10 /\ UNCHANGED x)
Inv == x <= TheOp
Spec == Init /\ [][Next]_x
====
