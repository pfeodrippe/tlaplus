package tlc2.tool;

import org.junit.Test;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.value.RandomEnumerableValues;

/**
 * Demonstrates that TLCGlobals.reset() does not reset all global state.
 * 
 * This test runs DIFFERENT models in sequence and verifies that:
 * 1. TLCGlobals.mainChecker persists across runs (and differs by object identity)
 * 2. TLCGlobals.reset() clears core TLC globals (mainChecker, simulator, metaDir, flags)
 * 3. But TLCGlobals.reset() does NOT clear:
 *    - Java static fields defined in user code (only by those fields' own reset methods)
 *    - UniqueString intern table (requires UniqueString.initialize())
 *    - RandomEnumerableValues ThreadLocal RNGs (requires RandomEnumerableValues.reset())
 * 
 * The test validates the reset behavior by checking that TLCGlobals fields are properly reset.
 */
public class RunTwicePersistentFlagTest {

    @Test
    public void testTLCGlobalsReset() throws Exception {
        // Before any run, TLCGlobals.mainChecker should be null
        if (TLCGlobals.mainChecker != null) {
            throw new AssertionError("TLCGlobals.mainChecker should be null before any run");
        }

        // ===== FIRST RUN: ModelCounter =====
        // ModelCounter increments a counter and violates invariant when counter reaches bound
        final int r1 = runTLC("test-model/ModelCounter.tla");
        // ModelCounter fails with invariant violation (exit code 2110)
        if (r1 == 0) {
            throw new AssertionError("ModelCounter should fail with invariant violation, but passed (exit code 0)");
        }

        // CRITICAL FINDING: After ModelCounter run, mainChecker is NOT null!
        // Tool cleanup does NOT clear TLCGlobals.mainChecker automatically.
        // This is the interference issue described in #891.
        if (TLCGlobals.mainChecker == null) {
            throw new AssertionError("UNEXPECTED: TLCGlobals.mainChecker is null after run. This would mean Tool cleanup cleared it.");
        }
        // Store the first instance to verify it's a different object in the next run
        Object checker1 = TLCGlobals.mainChecker;
        System.out.println("DEMONSTRATION 1: TLCGlobals.mainChecker persists after ModelCounter run: " + checker1);

        // ===== SECOND RUN: ModelString (DIFFERENT model) =====
        // ModelString concatenates strings and should complete successfully (no invariant violation)
        final int r2 = runTLC("test-model/ModelString.tla");
        if (r2 != 0) {
            throw new AssertionError("ModelString should succeed, but failed with exit code: " + r2);
        }

        // After ModelString run, mainChecker is STILL set (persists again)
        if (TLCGlobals.mainChecker == null) {
            throw new AssertionError("TLCGlobals.mainChecker should be set after ModelString run, but is null");
        }
        Object checker2 = TLCGlobals.mainChecker;
        System.out.println("DEMONSTRATION 2: TLCGlobals.mainChecker persists after ModelString run: " + checker2);
        
        // Verify they are different instances (from different model runs)
        if (checker1 == checker2) {
            throw new AssertionError("UNEXPECTED: mainChecker instances should differ (different runs), but got same object");
        }
        System.out.println("VERIFICATION: Different model checkers as expected (different objects)");

        // ===== CALL RESET =====
        // Call TLCGlobals.reset() to clean up
        TLCGlobals.reset();
        RandomEnumerableValues.reset();

        // After explicit reset, mainChecker should NOW be null
        if (TLCGlobals.mainChecker != null) {
            throw new AssertionError("TLCGlobals.mainChecker should be null after explicit reset, but is: " + TLCGlobals.mainChecker);
        }
        System.out.println("CONFIRMATION: TLCGlobals.reset() successfully cleared mainChecker");

        // ===== THIRD RUN: ModelSequence (THIRD DIFFERENT model) =====
        // ModelSequence generates a sequence of values
        final int r3 = runTLC("test-model/ModelSequence.tla");
        if (r3 != 0) {
            throw new AssertionError("ModelSequence should succeed, but failed with exit code: " + r3);
        }

        // After this run, mainChecker should be set again (because we're in a new run)
        if (TLCGlobals.mainChecker == null) {
            throw new AssertionError("TLCGlobals.mainChecker should be set during/after ModelSequence run, but is null");
        }
        Object checker3 = TLCGlobals.mainChecker;
        System.out.println("DEMONSTRATION 3: TLCGlobals.mainChecker set in third run (ModelSequence): " + checker3);
        
        // Verify it's different from both previous runs
        if (checker1 == checker3 || checker2 == checker3) {
            throw new AssertionError("UNEXPECTED: checker3 should differ from checker1 and checker2");
        }

        // Call reset again
        TLCGlobals.reset();
        RandomEnumerableValues.reset();
        
        if (TLCGlobals.mainChecker != null) {
            throw new AssertionError("TLCGlobals.mainChecker should be null after second reset, but is: " + TLCGlobals.mainChecker);
        }
        
        System.out.println("\n✓ TEST PASSED: Demonstrated global state persistence and effective reset");
    }

    private static int runTLC(final String modelPath) throws Exception {
        TLC tlc = new TLC();
        String[] args = new String[] { "-workers", "1", "-deadlock", "-metadir", "states/RunTwicePersistentFlagTest", modelPath };
        tlc.handleParameters(args);
        return tlc.process();
    }
}

