package tlc2.tool;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.value.RandomEnumerableValues;

/**
 * Manual test to verify TLC can run twice in same JVM.
 * This demonstrates the fix for GitHub issue #891.
 */
public class ManualRunTwiceTest {

    public static void main(String[] args) {
        System.out.println("=== First TLC Run (ModelA) ===");
        System.out.flush();
        int result1;
        try {
            result1 = runTLC("test-model/ModelA.tla");
            System.out.println("First run exit code: " + result1);
        } catch (Exception e) {
            System.err.println("First run failed: " + e.getMessage());
            e.printStackTrace();
            Runtime.getRuntime().halt(1);
            return;
        }

        System.out
                .println("\n=== Second TLC Run (ModelB) WITHOUT reset - expecting test to FAIL if globals persist ===");
        System.out.flush();

        // If TLC left global state set, fail the test to enforce that callers must
        // reset
        if (TLCGlobals.mainChecker != null || TLCGlobals.simulator != null) {
            System.err.println(
                    "ERROR: Global TLC state detected after first run. You must call TLCGlobals.reset() between runs.");
            System.err.println("Failing test because globals were not reset.");
            System.err.flush();
            Runtime.getRuntime().halt(2);
            return;
        }

        // If no globals detected (unlikely), proceed to run ModelB to show its behavior
        // First, call reset to demonstrate the successful path
        System.out.println("\nNow resetting globals and re-running ModelB to demonstrate success path...");
        System.out.flush();
        TLCGlobals.reset();
        RandomEnumerableValues.reset();
        System.out.println("✓ Global state reset complete");
        System.out.flush();
        int result2;
        try {
            result2 = runTLC("test-model/ModelB.tla");
            System.out.println("Second run exit code: " + result2);
        } catch (Exception e) {
            System.err.println("Second run failed: " + e.getMessage());
            e.printStackTrace();
            Runtime.getRuntime().halt(1);
            return;
        }

        System.out.println("\n✓✓✓ DONE: both runs completed (codes: " + result1 + ", " + result2 + ") ✓✓✓");
        System.out.flush();
        Runtime.getRuntime().halt(0);
    }

    private static Integer runTLC(final String modelPath) throws Exception {
        TLC tlc = new TLC();
        String[] args = new String[] {
                "-workers", "1",
                "-deadlock",
                "-metadir", "states/ManualRunTwiceTest",
                modelPath
        };
        tlc.handleParameters(args);
        return tlc.process();
    }
}
