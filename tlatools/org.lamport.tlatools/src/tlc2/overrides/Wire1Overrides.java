package tlc2.overrides;

import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Value;

/**
 * Java overrides for ModelWire1 operators.
 * These demonstrate operator override caching issues across multiple TLC runs.
 */
public class Wire1Overrides {

    @TLAPlusOperator(identifier = "wire_1_check", module = "ModelWire1")
    public static Value wire_1_check(Value _main_var) {
        // Just return TRUE - the actual check is done in TLA+
        return BoolValue.ValTrue;
    }

    @TLAPlusOperator(identifier = "wire_1_invariant", module = "ModelWire1")
    public static Value wire_1_invariant(Value _main_var) {
        // Just return TRUE - the actual invariant is checked in TLA+
        return BoolValue.ValTrue;
    }
}
