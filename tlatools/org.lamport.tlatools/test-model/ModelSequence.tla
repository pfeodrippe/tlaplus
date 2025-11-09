---- MODULE ModelSequence ----
EXTENDS Sequences, Naturals

VARIABLE seq

Init == seq = <<>>

Next == 
  IF Len(seq) < 4 THEN
    seq' = Append(seq, Len(seq) + 1)
  ELSE
    UNCHANGED seq

\* Invariant: sequence length should not exceed 4
Inv == Len(seq) <= 4

====
