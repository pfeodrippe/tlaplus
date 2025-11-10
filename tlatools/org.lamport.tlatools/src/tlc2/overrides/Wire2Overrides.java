package tlc2.overrides;

import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Value;

/**
 * Java overrides for ModelWire2 operators.
 * These demonstrate operator override caching issues across multiple TLC runs.
 */
public class Wire2Overrides {

    @TLAPlusOperator(identifier = "wire_2_check", module = "ModelWire2")
    public static Value wire_2_check(Value _main_var) {
        // Just return TRUE - the actual check is done in TLA+
        return BoolValue.ValTrue;
    }

    @TLAPlusOperator(identifier = "wire_2_invariant", module = "ModelWire2")
    public static Value wire_2_invariant(Value _main_var) {
        // Just return TRUE - the actual invariant is checked in TLA+
        return BoolValue.ValTrue;
    }
}
