package tlc2.tool;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.value.RandomEnumerableValues;
import tlc2.overrides.PersistentFlagImpl;

public class ManualRunPersistentFlagTest {
    public static void main(String[] args) throws Exception {
        // Ensure flag is clear
        PersistentFlagImpl.clearFlag();

        // Run ModelA_Flag (should execute SetFlag during next-state)
        System.out.println("Running ModelA_Flag...");
        TLC tlc1 = new TLC();
    tlc1.handleParameters(new String[] {"-workers", "1", "-deadlock", "-metadir", "states/ManualRunPersistentFlagTest", "-I", "test-model", "test-model/ModelA_Flag.tla"});
        int r1 = tlc1.process();
        System.out.println("ModelA_Flag exit code: " + r1);

        // Run ModelB_Flag without reset: should observe flag and succeed (exit 0)
        System.out.println("Running ModelB_Flag without reset...");
        TLC tlc2 = new TLC();
    tlc2.handleParameters(new String[] {"-workers", "1", "-deadlock", "-metadir", "states/ManualRunPersistentFlagTest", "-I", "test-model", "test-model/ModelB_Flag.tla"});
        int r2 = tlc2.process();
        System.out.println("ModelB_Flag exit code (no reset): " + r2);

        // Reset TLC globals
        TLCGlobals.reset();
        RandomEnumerableValues.reset();
        System.out.println("Called TLCGlobals.reset() and RandomEnumerableValues.reset()");

        // Check if Java-side flag is still set
        System.out.println("PersistentFlagImpl.isSet() = " + PersistentFlagImpl.isSet());

        // Run ModelB_Flag again
        System.out.println("Running ModelB_Flag after TLCGlobals.reset()...");
        TLC tlc3 = new TLC();
    tlc3.handleParameters(new String[] {"-workers", "1", "-deadlock", "-metadir", "states/ManualRunPersistentFlagTest", "-I", "test-model", "test-model/ModelB_Flag.tla"});
        int r3 = tlc3.process();
        System.out.println("ModelB_Flag exit code (after reset): " + r3);

        // Clear flag and run again
        PersistentFlagImpl.clearFlag();
        System.out.println("Cleared persistent flag.");
    TLC tlc4 = new TLC();
    tlc4.handleParameters(new String[] {"-workers", "1", "-deadlock", "-metadir", "states/ManualRunPersistentFlagTest", "-I", "test-model", "test-model/ModelB_Flag.tla"});
        int r4 = tlc4.process();
        System.out.println("ModelB_Flag exit code (after clearing flag): " + r4);

        System.exit(0);
    }
}
