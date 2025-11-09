package tlc2.overrides;

import tlc2.tool.TLCGlobals;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Value;
import tlc2.overrides.TLAPlusOperator;

/**
 * Java override for RunFlagModule.CheckGlobalsSet.
 * Returns TRUE iff TLCGlobals.mainChecker or TLCGlobals.simulator is non-null.
 */
public class RunFlagModuleImpl {

    @TLAPlusOperator(identifier = "CheckGlobalsSet", module = "RunFlagModule")
    public static Value CheckGlobalsSet() {
        return (TLCGlobals.mainChecker != null || TLCGlobals.simulator != null)
                ? BoolValue.ValTrue
                : BoolValue.ValFalse;
    }
}
