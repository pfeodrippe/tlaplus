package tlc2.overrides;

import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Value;
import tlc2.overrides.TLAPlusOperator;

/**
 * Deterministic persistent flag used for tests.
 * ModelA_Flag calls SetFlag (Java override) which sets this flag to true.
 * ModelB_Flag calls CheckFlag which returns the flag value.
 */
public class PersistentFlagImpl {

    private static volatile boolean flag = false;

    @TLAPlusOperator(identifier = "SetFlag", module = "FlagSetterModule")
    public static Value SetFlag() {
        flag = true;
        return BoolValue.ValTrue;
    }

    @TLAPlusOperator(identifier = "CheckFlag", module = "FlagSetterModule")
    public static Value CheckFlag() {
        return flag ? BoolValue.ValTrue : BoolValue.ValFalse;
    }

    // Utility used by unit tests to clear the flag deterministically.
    public static void clearFlag() {
        flag = false;
    }

    public static boolean isSet() {
        return flag;
    }
}
