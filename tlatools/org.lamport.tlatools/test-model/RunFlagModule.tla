--------------------------- MODULE RunFlagModule -----------------------
\* This module declares an operator that is implemented by a Java override.
\* The Java override returns TRUE iff TLC global state (mainChecker or simulator)
\* is set in the current JVM. This allows tests to observe whether a previous
\* TLC run left global state set.

CheckGlobalsSet == FALSE

=============================================================================
