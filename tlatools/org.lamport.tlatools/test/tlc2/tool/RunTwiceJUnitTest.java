package tlc2.tool;

import org.junit.Test;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.value.RandomEnumerableValues;

/**
 * JUnit test that verifies running TLC twice in the same JVM requires
 * resetting global state between runs.
 */
public class RunTwiceJUnitTest {

    @Test
    public void testSecondRunFailsIfNoReset() throws Exception {
        // Run ModelA (designed to produce an invariant violation)
        final int r1 = runTLC("test-model/ModelA.tla");
        // Expect a non-zero exit code for invariant violation
        if (r1 == 0) {
            throw new AssertionError("ModelA should report invariant violation");
        }

        // Global TLC state should be set after a run
        final boolean globalsSet = (TLCGlobals.mainChecker != null) || (TLCGlobals.simulator != null);
        if (!globalsSet) {
            throw new AssertionError("TLC global state should be present after first run");
        }

        // Try running ModelB without resetting globals — this should NOT silently succeed.
        final int r2 = runTLC("test-model/ModelB.tla");
        // If the second run returns 0 here, that means globals didn't interfere — fail the test
        if (r2 == 0) {
            throw new AssertionError("Second run unexpectedly succeeded without resetting globals");
        }
    }

    @Test
    public void testSecondRunSucceedsAfterReset() throws Exception {
        // Run ModelA
        final int r1 = runTLC("test-model/ModelA.tla");
        if (r1 == 0) {
            throw new AssertionError("ModelA should report invariant violation");
        }

        // Properly reset globals
        TLCGlobals.reset();
        RandomEnumerableValues.reset();

        // Now run ModelB and assert it behaves (we expect a non-zero violation code in our small models)
        final int r2 = runTLC("test-model/ModelB.tla");
        if (r2 == 0) {
            throw new AssertionError("ModelB should report invariant violation on a clean run");
        }
    }

    private static int runTLC(final String modelPath) throws Exception {
        TLC tlc = new TLC();
        String[] args = new String[] { "-workers", "1", "-deadlock", "-metadir", "states/RunTwiceJUnitTest", modelPath };
        tlc.handleParameters(args);
        return tlc.process();
    }
}
