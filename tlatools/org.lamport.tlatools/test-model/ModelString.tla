---- MODULE ModelString ----
EXTENDS Sequences, Naturals

VARIABLE str

Init == str = ""

Next == 
  IF Len(str) < 2 THEN
    str' = str \o "x"
  ELSE
    UNCHANGED str

\* Invariant: string length should never exceed 2 characters
Inv == Len(str) <= 2

====
