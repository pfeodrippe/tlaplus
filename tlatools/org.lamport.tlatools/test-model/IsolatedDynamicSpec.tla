---- MODULE IsolatedDynamicSpec ----
EXTENDS Integers
VARIABLE x
TheOp == 4 + 4
Init == x = 0
Action == ( /\ x < 8 /\ x' = x + 1 ) \/ ( /\ x = 8 /\ UNCHANGED x )
Next == Action
Inv == x <= TheOp
Spec == Init /\ [][Next]_x
====
