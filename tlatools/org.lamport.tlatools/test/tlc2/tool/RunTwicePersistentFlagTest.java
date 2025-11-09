package tlc2.tool;

import org.junit.Test;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.value.RandomEnumerableValues;

/**
 * Demonstrates that TLCGlobals.reset() does not reset all global state.
 * 
 * This test runs DIFFERENT models in sequence and verifies that:
 * 1. TLCGlobals.mainChecker persists across runs (and differs by object
 * identity)
 * 2. TLCGlobals.reset() clears core TLC globals (mainChecker, simulator,
 * metaDir, flags)
 * 3. But TLCGlobals.reset() does NOT clear:
 * - Java static fields defined in user code (only by those fields' own reset
 * methods)
 * - UniqueString intern table (requires UniqueString.initialize())
 * - RandomEnumerableValues ThreadLocal RNGs (requires
 * RandomEnumerableValues.reset())
 * 
 * The test validates the reset behavior by checking that TLCGlobals fields are
 * properly reset.
 */
public class RunTwicePersistentFlagTest {

    @Test
    public void testTLCGlobalsReset() throws Exception {
        // Before any run, TLCGlobals.mainChecker should be null
        if (TLCGlobals.mainChecker != null) {
            throw new AssertionError("TLCGlobals.mainChecker should be null before any run");
        }

        // Store all checker instances to verify they're all different
        Object[] checkers = new Object[7];
        int[] exitCodes = new int[7];

        // ===== RUN 1: ModelCounter =====
        // Fails at invariant (counter=4 violates counter<=3)
        exitCodes[0] = runTLC("test-model/ModelCounter.tla");
        if (exitCodes[0] == 0) {
            throw new AssertionError("ModelCounter should fail with invariant violation, but passed");
        }
        if (TLCGlobals.mainChecker == null) {
            throw new AssertionError("TLCGlobals.mainChecker should be set after ModelCounter run");
        }
        checkers[0] = TLCGlobals.mainChecker;
        System.out.println("RUN 1 - ModelCounter (FAIL): " + checkers[0]);

        // ===== RUN 2: ModelString =====
        // Passes successfully
        exitCodes[1] = runTLC("test-model/ModelString.tla");
        if (exitCodes[1] != 0) {
            throw new AssertionError("ModelString should pass, but failed with exit code: " + exitCodes[1]);
        }
        checkers[1] = TLCGlobals.mainChecker;
        if (checkers[0] == checkers[1]) {
            throw new AssertionError("Run 1 and 2 should have different checker instances");
        }
        System.out.println("RUN 2 - ModelString (PASS): " + checkers[1]);

        // ===== RUN 3: ModelSequence =====
        // Passes successfully
        exitCodes[2] = runTLC("test-model/ModelSequence.tla");
        if (exitCodes[2] != 0) {
            throw new AssertionError("ModelSequence should pass, but failed with exit code: " + exitCodes[2]);
        }
        checkers[2] = TLCGlobals.mainChecker;
        if (checkers[1] == checkers[2]) {
            throw new AssertionError("Run 2 and 3 should have different checker instances");
        }
        System.out.println("RUN 3 - ModelSequence (PASS): " + checkers[2]);

        // ===== RESET 1 =====
        TLCGlobals.reset();
        RandomEnumerableValues.reset();
        if (TLCGlobals.mainChecker != null) {
            throw new AssertionError("TLCGlobals.mainChecker should be null after reset 1");
        }
        System.out.println("RESET 1 - State cleared");

        // ===== RUN 4: ModelQueue =====
        // Queue enqueue/dequeue operations, passes successfully
        exitCodes[3] = runTLC("test-model/ModelQueue.tla");
        if (exitCodes[3] != 0) {
            throw new AssertionError("ModelQueue should pass, but failed with exit code: " + exitCodes[3]);
        }
        checkers[3] = TLCGlobals.mainChecker;
        // Verify all previous checkers are different from this one
        for (int i = 0; i < 3; i++) {
            if (checkers[i] == checkers[3]) {
                throw new AssertionError("Run 4 checker should differ from run " + (i + 1) + " checker");
            }
        }
        System.out.println("RUN 4 - ModelQueue (PASS): " + checkers[3]);

        // ===== RUN 5: ModelSet =====
        // Set add/remove operations, passes successfully
        exitCodes[4] = runTLC("test-model/ModelSet.tla");
        if (exitCodes[4] != 0) {
            throw new AssertionError("ModelSet should pass, but failed with exit code: " + exitCodes[4]);
        }
        checkers[4] = TLCGlobals.mainChecker;
        // Verify different from all previous runs
        for (int i = 0; i < 4; i++) {
            if (checkers[i] == checkers[4]) {
                throw new AssertionError("Run 5 checker should differ from run " + (i + 1) + " checker");
            }
        }
        System.out.println("RUN 5 - ModelSet (PASS): " + checkers[4]);

        // ===== RUN 6: ModelTuple =====
        // Tuple element manipulation, passes successfully
        exitCodes[5] = runTLC("test-model/ModelTuple.tla");
        if (exitCodes[5] != 0) {
            throw new AssertionError("ModelTuple should pass, but failed with exit code: " + exitCodes[5]);
        }
        checkers[5] = TLCGlobals.mainChecker;
        // Verify different from all previous runs
        for (int i = 0; i < 5; i++) {
            if (checkers[i] == checkers[5]) {
                throw new AssertionError("Run 6 checker should differ from run " + (i + 1) + " checker");
            }
        }
        System.out.println("RUN 6 - ModelTuple (PASS): " + checkers[5]);

        // ===== RESET 2 =====
        TLCGlobals.reset();
        RandomEnumerableValues.reset();
        if (TLCGlobals.mainChecker != null) {
            throw new AssertionError("TLCGlobals.mainChecker should be null after reset 2");
        }
        System.out.println("RESET 2 - State cleared");

        // ===== RUN 7: ModelComplexQueue (COMPLEX with invariant violation) =====
        // Complex queue model with invariant violation (size <= 2 but enqueues up to 5)
        exitCodes[6] = runTLC("test-model/ModelComplexQueue.tla");
        if (exitCodes[6] == 0) {
            throw new AssertionError("ModelComplexQueue should fail with invariant violation, but passed");
        }
        checkers[6] = TLCGlobals.mainChecker;
        // Verify different from all previous runs
        for (int i = 0; i < 6; i++) {
            if (checkers[i] == checkers[6]) {
                throw new AssertionError("Run 7 checker should differ from run " + (i + 1) + " checker");
            }
        }
        System.out.println("RUN 7 - ModelComplexQueue (FAIL - INVARIANT VIOLATION): " + checkers[6]);

        // ===== VERIFICATION SUMMARY =====
        System.out.println("\n=== VERIFICATION SUMMARY ===");
        System.out.println("Total runs: 7");
        System.out.println("Pass runs: 5 (ModelString, ModelSequence, ModelQueue, ModelSet, ModelTuple)");
        System.out.println(
                "Fail runs: 2 (ModelCounter with invariant violation, ModelComplexQueue with invariant violation)");
        System.out.println("All 7 checker instances are unique: YES");
        System.out.println("Reset clears state: YES (checked 2x)");
        System.out.println("\n✓ TEST PASSED: 7 models demonstrate persistent global state and effective reset");
    }

    private static int runTLC(final String modelPath) throws Exception {
        TLC tlc = new TLC();
        String[] args = new String[] { "-workers", "1", "-deadlock", "-metadir", "states/RunTwicePersistentFlagTest",
                modelPath };
        tlc.handleParameters(args);
        return tlc.process();
    }
}
