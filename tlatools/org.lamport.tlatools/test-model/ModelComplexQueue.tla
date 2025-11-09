---- MODULE ModelComplexQueue ----
(* A complex model with accumulation and processing phases *)
EXTENDS Naturals, Sequences

VARIABLE count, phase, items

Init == 
  /\ count = 0
  /\ phase = "init"
  /\ items = 0

Next == 
  \/ \* Phase 1: Accumulate items
     /\ phase = "init"
     /\ count < 3
     /\ count' = count + 1
     /\ items' = items + 1
     /\ UNCHANGED phase
     
  \/ \* Transition from init to process
     /\ phase = "init"
     /\ count >= 3
     /\ phase' = "process"
     /\ count' = count + 1
     /\ UNCHANGED items
     
  \/ \* Phase 2: Process items
     /\ phase = "process"
     /\ count < 6
     /\ count' = count + 1
     /\ items' = items + 1
     /\ UNCHANGED phase
     
  \/ \* Transition to done
     /\ phase = "process"
     /\ count >= 6
     /\ phase' = "done"
     /\ UNCHANGED <<count, items>>

\* INVARIANT: items should never exceed 2, but we increment it 5+ times
\* This will be violated during "process" phase
Inv == items <= 2

====
