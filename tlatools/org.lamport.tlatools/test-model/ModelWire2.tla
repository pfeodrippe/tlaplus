---- MODULE ModelWire2 ----
EXTENDS Integers, TLC

VARIABLES balance, phase

vars == <<balance, phase>>

Init == 
    /\ balance = 10
    /\ phase = "check_and_withdraw"

CheckAndWithdraw ==
    /\ phase = "check_and_withdraw"
    /\ phase' = "deposit"
    /\ balance' = balance - 5

Deposit ==
    /\ phase = "deposit"
    /\ phase' = "done"
    /\ balance' = balance + 3

Next == CheckAndWithdraw \/ Deposit

\* Invariant for wire model 2 - DIFFERENT NAME than Wire1Invariant
Wire2Invariant == balance >= 0

Spec == Init /\ [][Next]_vars

====
