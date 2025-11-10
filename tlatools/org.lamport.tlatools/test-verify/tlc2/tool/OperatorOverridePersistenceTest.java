package tlc2.tool;

import tlc2.TLC;
import tlc2.overrides.TLCOverrides;
import tlc2.util.RandomEnumerableValues;
import util.UniqueString;

/**
 * Test that demonstrates operator override persistence across multiple TLC runs in the same JVM.
 * 
 * The test runs two different specs with different initial values for global variables.
 * If operator overrides (Java classes that implement TLA+ operators) are not properly reset,
 * the second run will use cached overrides from the first run, causing incorrect behavior.
 */
public class OperatorOverridePersistenceTest {

    public static void main(String[] args) throws Exception {
        System.out.println("=== RUN 1: ModelA (alice=5) ===");
        runTLC("spec_a.tla");
        System.out.println("\nAfter Run 1, resetting TLC globals...");
        TLCGlobals.reset();
        RandomEnumerableValues.reset();
        UniqueString.initialize();
        System.out.println("Reset complete.\n");

        System.out.println("=== RUN 2: ModelB (alice=1, should NOT have alice=5 from Run 1) ===");
        runTLC("spec_b.tla");
        System.out.println("\nTest complete.");
    }

    private static void runTLC(String specFile) throws Exception {
        // Simulate TLC command: java -jar tla2tools.jar spec_a.tla
        String[] tlcArgs = {
            "-workers", "1",
            "-fp", "64",
            specFile
        };
        try {
            TLC.main(tlcArgs);
        } catch (Exception e) {
            System.err.println("TLC run failed: " + e.getMessage());
            e.printStackTrace();
        }
    }
}
