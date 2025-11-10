---- MODULE ModelWire1 ----
EXTENDS Integers, TLC

VARIABLES account, pc

vars == <<account, pc>>

Init == 
    /\ account = 10
    /\ pc = "check"

CheckFunds ==
    /\ pc = "check"
    /\ pc' = "withdraw"
    /\ UNCHANGED account

Withdraw ==
    /\ pc = "withdraw"
    /\ pc' = "deposit"
    /\ account' = account - 5

Deposit ==
    /\ pc = "deposit"
    /\ pc' = "done"
    /\ account' = account + 3

Next == CheckFunds \/ Withdraw \/ Deposit

\* Invariant for wire model 1 - UNIQUE NAME
Wire1Invariant == account >= 0

Spec == Init /\ [][Next]_vars

====
