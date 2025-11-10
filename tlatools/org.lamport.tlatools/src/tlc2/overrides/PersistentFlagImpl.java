package tlc2.overrides;

import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Value;

/**
 * Deterministic persistent flag used for demonstrating JVM-side state persistence.
 * 
 * SetFlag: Java override that returns TRUE and has a side effect of setting persistentFlag = true.
 *          This way, SetFlag /\ ... in TLA+ will always succeed and trigger the side effect.
 * GetFlag: Java override that returns the current value of persistentFlag.
 * 
 * This class demonstrates that Java static fields persist across TLC runs in the same JVM
 * and are not cleared by TLCGlobals.reset().
 */
public class PersistentFlagImpl {

    private static volatile boolean persistentFlag = false;

    @TLAPlusOperator(identifier = "SetFlag", module = "FlagSetterModule")
    public static Value SetFlag() {
        // Side effect: set the persistent flag
        persistentFlag = true;
        // Return TRUE so that conjunctions in TLA+ don't short-circuit
        return BoolValue.ValTrue;
    }

    @TLAPlusOperator(identifier = "GetFlag", module = "FlagSetterModule")
    public static Value GetFlag() {
        return persistentFlag ? BoolValue.ValTrue : BoolValue.ValFalse;
    }

    // Utility used by unit tests to clear the flag deterministically.
    public static void clearFlag() {
        persistentFlag = false;
    }

    public static boolean isSet() {
        return persistentFlag;
    }
}
