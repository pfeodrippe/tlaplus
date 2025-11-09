package tlc2.tool;

import org.junit.Assert;
import org.junit.Test;
import tlc2.TestMPRecorder;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.value.RandomEnumerableValues;
import util.ToolIO;
import util.UniqueString;

/**
 * Test that TLC can be run twice in the same JVM.
 * This addresses issue #891: https://github.com/tlaplus/tlaplus/issues/891
 */
public class RunTwiceTest extends ModelCheckerTestCase {

	public RunTwiceTest() {
		super("RunTwice", EC.ExitStatus.SUCCESS);
	}

	@Test
	public void testSpec() {
		// Run TLC the first time
		Assert.assertTrue("First run should finish", recorder.recorded(EC.TLC_FINISHED));
		Assert.assertTrue("First run should succeed", recorder.recordedWithStringValues(EC.TLC_STATS, "4", "4", "0"));
		Assert.assertFalse("First run should have no errors", recorder.recorded(EC.GENERAL));

		// Reset TLC global state to allow second run
		TLCGlobals.reset();
		UniqueString.initialize();
		RandomEnumerableValues.reset();
		
		// Create a new recorder for the second run
		TestMPRecorder newRecorder = new TestMPRecorder();
		MP.setRecorder(newRecorder);
		
		// Reset ToolIO user dir for second run
		ToolIO.setUserDir(BASE_PATH + path);
		
		// Run TLC a second time by calling setUp() again, which re-initializes TLC
		try {
			// Call setUp to re-initialize TLC for second run
			setUp();
			
			// If we get here without exceptions, check if the second run works
			Assert.assertTrue("Second run should finish", newRecorder.recorded(EC.TLC_FINISHED));
			Assert.assertTrue("Second run should succeed", newRecorder.recordedWithStringValues(EC.TLC_STATS, "4", "4", "0"));
			Assert.assertFalse("Second run should have no errors", newRecorder.recorded(EC.GENERAL));
			
			System.out.println("SUCCESS: TLC ran twice in the same JVM!");
		} catch (Exception e) {
			// Expected to fail due to global state issues
			throw new AssertionError("Cannot run TLC twice in same JVM due to global state issues: " + e.getMessage(), e);
		}
	}
}


