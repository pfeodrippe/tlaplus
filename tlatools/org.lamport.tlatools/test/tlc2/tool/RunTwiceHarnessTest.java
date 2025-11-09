package tlc2.tool;

import org.junit.Test;

import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.value.RandomEnumerableValues;

/**
 * Harnessed test that runs two small models under the project's test harness
 * to verify that clients must reset globals between runs.
 */
public class RunTwiceHarnessTest extends CommonTestCase {

    public RunTwiceHarnessTest() {
        super(new TestMPRecorder());
    }

    @Test
    public void testRunTwiceWithAndWithoutReset() throws Exception {
        // First run: ModelA
        MP.setRecorder(recorder);
        final TLC tlc1 = new TLC();
        tlc1.handleParameters(new String[] { BASE_PATH + "ModelA" });
        final int r1 = tlc1.process();

        // ModelA is designed to violate an invariant; expect non-zero exit
        if (r1 == 0) {
            throw new AssertionError("ModelA should not return 0");
        }
        if (!recorder.recorded(EC.TLC_FINISHED)) {
            throw new AssertionError("First run should record TLC finished");
        }

        // Second run without resetting globals: we expect it to fail or misbehave
        final TestMPRecorder secondRecorder = new TestMPRecorder();
        MP.setRecorder(secondRecorder);

        final TLC tlc2 = new TLC();
        tlc2.handleParameters(new String[] { BASE_PATH + "ModelB" });
        final int r2 = tlc2.process();

        // If globals were set by the first run, the second run should not silently succeed.
        if (TLCGlobals.mainChecker != null || TLCGlobals.simulator != null) {
            if (r2 == 0) {
                throw new AssertionError("Second run unexpectedly returned success without reset");
            }
        }

        // Now, demonstrate correct usage: reset globals and run ModelB cleanly
        TLCGlobals.reset();
        RandomEnumerableValues.reset();
        final TestMPRecorder thirdRecorder = new TestMPRecorder();
        MP.setRecorder(thirdRecorder);

        final TLC tlc3 = new TLC();
        tlc3.handleParameters(new String[] { BASE_PATH + "ModelB" });
        final int r3 = tlc3.process();
        if (r3 == 0) {
            throw new AssertionError("ModelB should report invariant violation on a clean run");
        }
        if (!thirdRecorder.recorded(EC.TLC_FINISHED)) {
            throw new AssertionError("Clean run should record TLC finished");
        }
    }
}
