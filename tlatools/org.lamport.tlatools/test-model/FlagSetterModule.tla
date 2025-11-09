--------------------------- MODULE FlagSetterModule -----------------------
\* A small module declaring two operators implemented in Java overrides:
\*   SetFlag  -- Java override: sets a persistent Java static flag to true, returns TRUE
\*   GetFlag  -- Java override: returns the current value of the persistent flag

SetFlag == TRUE
GetFlag == FALSE

=============================================================================
