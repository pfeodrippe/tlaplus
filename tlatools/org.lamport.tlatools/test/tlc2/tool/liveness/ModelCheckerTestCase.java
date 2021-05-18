/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool.liveness;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.junit.After;
import org.junit.Assume;
import org.junit.Before;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.TLCRunner;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.output.MP;
import tlc2.tool.CommonTestCase;
import tlc2.tool.ModelChecker;
import tlc2.tool.TLCStateInfo;
import util.FileUtil;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import util.TLAConstants;
import util.ToolIO;

public abstract class ModelCheckerTestCase extends CommonTestCase {

	protected final static String teSpecSuffix = "_" + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + "_2000000000";
	
	protected String path = "";
	protected String spec;
	protected String[] extraArguments = new String[0];
	protected TLC tlc;
	protected int actualExitStatus = -1;
	protected int expectedExitStatus = ExitStatus.SUCCESS;

	public ModelCheckerTestCase(String spec) {
		this(spec, ExitStatus.SUCCESS);
	}

	public ModelCheckerTestCase(String spec, final int exitStatus) {
		this(spec, "", exitStatus);
	}

	public ModelCheckerTestCase(String spec, String path) {
		this(spec, path, ExitStatus.SUCCESS);
	}
	
	public ModelCheckerTestCase(String spec, String[] extraArguments) {
		this(spec, "", extraArguments, ExitStatus.SUCCESS);
	}
	
	public ModelCheckerTestCase(String spec, String[] extraArguments, final int exitStatus) {
		this(spec, "", extraArguments, exitStatus);
	}
	
	public ModelCheckerTestCase(String spec, String path, String[] extraArguments) {
		this(spec, path, extraArguments, ExitStatus.SUCCESS);
	}
	
	public ModelCheckerTestCase(String spec, String path, String[] extraArguments, final int exitStatus) {
		this(spec, path, exitStatus);
		this.extraArguments  = extraArguments; 
	}
	
	public ModelCheckerTestCase(final String spec, final String path, final int exitStatus) {
		super(new TestMPRecorder());
		this.spec = spec;
		this.path = path;
		this.expectedExitStatus = exitStatus;
	}

	protected void beforeSetUp() {
		// No-op
	}

	// Use it to indicate that the test will read the generated
	// TE spec file instead of running the original spec.
	protected boolean isTESpec() {
		return false;
	}

	private String originalTESpecPath() {
		return System.getProperty("user.dir") + File.separator + this.spec;
	}

	private String clonedTESpecPath() {
		return BASE_PATH + this.path + File.separator + this.spec;
	}	

	private void checkTESpecAssumption() {
		Path sourcePath = Paths.get(originalTESpecPath() + TLAConstants.Files.TLA_EXTENSION);
		Path destPath = Paths.get(clonedTESpecPath() + TLAConstants.Files.TLA_EXTENSION);

		// First check if the file is already moved to the correct path.
		// If it doesn't, check with `Assume` that the generated file exists
		// in the original path.
		if (destPath.toFile().isFile()) {
			return;
		} else {
			Assume.assumeTrue("No TE spec was generated, please run test with original spec", sourcePath.toFile().isFile());
		}
	}

	private void moveTESpecFiles() {
		// Move generated files from their original location (user.dir) to the same folder
		// as the original TLA spec so we can run the generated TE spec.
		// First the TLA file.
		Path sourcePath = Paths.get(originalTESpecPath() + TLAConstants.Files.TLA_EXTENSION);
		Path destPath = Paths.get(clonedTESpecPath() + TLAConstants.Files.TLA_EXTENSION);	
		
		try {
			Files.move(sourcePath, destPath, StandardCopyOption.REPLACE_EXISTING);
		} catch (IOException exception) {
			fail(exception.toString());
		}

		// Then we move the config file.
		sourcePath = Paths.get(originalTESpecPath() + TLAConstants.Files.CONFIG_EXTENSION);
		destPath = Paths.get(clonedTESpecPath() + TLAConstants.Files.CONFIG_EXTENSION);
		try {
			Files.move(sourcePath, destPath, StandardCopyOption.REPLACE_EXISTING);
		} catch (IOException exception) {
			fail(exception.toString());
		}
	}

	private void removeGeneratedFiles(String originalPath, String clonedPath) {
        // Remove generated files, if any.
        new File(originalPath + TLAConstants.Files.TLA_EXTENSION).delete();
        new File(originalPath + TLAConstants.Files.CONFIG_EXTENSION).delete();
        new File(clonedPath + TLAConstants.Files.TLA_EXTENSION).delete();
        new File(clonedPath + TLAConstants.Files.CONFIG_EXTENSION).delete();
    }

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	@Before
	public void setUp() {
		if (!isTESpec()) {
			// Remove any generated file before running a original spec.
			removeGeneratedFiles(originalTESpecPath() + teSpecSuffix, clonedTESpecPath() + teSpecSuffix);
		} else {
			checkTESpecAssumption();
			
			// If it's a TE spec run, move TE spec files so they are in the
			// correct path.
			moveTESpecFiles();			
		}

		beforeSetUp();		
		
		// some tests might want to access the liveness graph after model
		// checking completed. Thus, prevent the liveness graph from being
		// closed too earlier.
		System.setProperty(ModelChecker.class.getName() + ".vetoCleanup", "true");

		// Timestamps for traces generated by the trace expression writer (trace explorer)
		// will have the same suffix so it's easy to know beforehand the name of the
		// file.
		System.setProperty("TLC_TRACE_EXPLORER_TIMESTAMP", "2000000000");

		// Generate TE spec with JSON generation uncommented so we can test with the original
		// trace.
		System.setProperty("TLC_TRACE_EXPLORER_JSON_UNCOMMENTED", "true");

		try {
			// TEST_MODEL is where TLC should look for user defined .tla files
			ToolIO.setUserDir(BASE_PATH + path);
			
			MP.setRecorder(recorder);
			
			// Increase the liveness checking threshold to prevent liveness
			// checking of an incomplete graph. Most tests check that the 
			// state queue is empty and fail if not. This is only given 
			// when liveness checking is executed when all states have been
			// generated.
			TLCGlobals.livenessThreshold = getLivenessThreshold();
			
			tlc = new TLC();
			tlc.setResolver(getResolver());
			// * We want *no* deadlock checking to find the violation of the
			// temporal formula
			// * We use (unless overridden) a single worker to simplify
			// debugging by taking out threading
			// * MC is the name of the TLA+ specification to be checked (the file
			// is placed in TEST_MODEL
			final List<String> args = new ArrayList<String>(6);
			
			// *Don't* check for deadlocks. All tests are interested in liveness
			// checks which are shielded away by deadlock checking. TLC finds a
			// deadlock (if it exists) before it finds most liveness violations.
			if (!checkDeadLock()) {
				args.add("-deadlock");
			}
			
			if (getNumberOfThreads() == 1 && runWithDebugger()) {
				args.add("-debugger");
				args.add(String.format("nosuspend,port=%s,nohalt", 1025 + new Random().nextInt(64540)));
			}
			
			if (noGenerateSpec()) {
				args.add("-noGenerateSpecTE");
			}
			
			if (noRandomFPandSeed()) {
				args.add("-fp");
				args.add("0");
				// Deterministic simulation (order in which actions are explored).
				args.add("-seed");
				args.add("1");
			}
			
			if (doCoverage()) {
				args.add("-coverage");
				args.add("1");
			}
			
			args.add("-workers");
			args.add(Integer.toString(getNumberOfThreads()));
			
			// Never create checkpoints. They distort performance tests and are
			// of no use anyway.
			args.add("-checkpoint");
			args.add(Integer.toString(doCheckpoint()));
			
			// Always print the state graph in dot file notation.
			if (doDump()) {
				args.add("-dump");
				args.add("dot");
				args.add("${metadir}" + FileUtil.separator + getClass().getCanonicalName() + ".dot");
			}

			args.addAll(Arrays.asList(extraArguments));
			
			args.add(spec);
			tlc.handleParameters(args.toArray(new String[args.size()]));
			
			// Run the ModelChecker
			final int errorCode = tlc.process();
			actualExitStatus = EC.ExitStatus.errorConstantToExitStatus(errorCode);
			
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}

	protected boolean noRandomFPandSeed() {
		return true;
	}

	protected boolean runWithDebugger() {
		return true;
	}

	protected double getLivenessThreshold() {
		return Double.MAX_VALUE;
	}

	protected FilenameToStream getResolver() {
		return new SimpleFilenameToStream();
	}

	protected boolean noGenerateSpec() {
		return false;
	}

	// There are tests which we do not want to prevent
	// the spec to generate TE files, but also we don't
	// want or need (or can't because of some bug) to run
	// the generated spec.
	protected boolean doNotTestTESpec() {
		return false;
	}

	protected void beforeTearDown() {
		// No-op
	}

	protected void runTESpec() {
		// If we don't generate a TE spec or if there is no error trace or if the test
		// asks for it, we do nothing here.
		if (noGenerateSpec() || recorder.getRecords(EC.TLC_STATE_PRINT2) == null || doNotTestTESpec()) {
			return;
		}

		List<String> extraArgs = new ArrayList<String>(Arrays.asList(this.extraArguments));

		// Move generated files from their original location (user.dir) to the same folder
		// as the original TLA spec so we can run the generated TE spec.
		// First the TLA file.
		Path sourcePath = Paths.get(originalTESpecPath() + TLAConstants.Files.TLA_EXTENSION);

		// Check that no TE spec was generated for a throwed exception with at max one state.
		if (TLCGlobals.throwedException && recorder.getRecords(EC.TLC_STATE_PRINT2).size() <= 1) {
			if (sourcePath.toFile().exists()) {
				fail("No TE spec should be generated for cases where an exception was thrown and the error trace has at max one state, but " + sourcePath.toString() + " was generated.");				
			}
			return;
		}

		// For cases where we have the `-continue` arg passed to TLC, we make sure that
		// no TE spec was generated.
		final int continueIdx = extraArgs.indexOf("-continue");
		if (continueIdx >= 0) {
			if (sourcePath.toFile().exists()) {
				fail("No TE spec should be generated when a TLC arg is \"-continue\", but " + sourcePath.toString() + " was generated.");
			}
			return;
		}

		// For cases where we have the `-recover` arg passed to TLC, we make sure that
		// no TE spec was generated.
		final int recoverIdx = extraArgs.indexOf("-recover");
		if (recoverIdx >= 0) {
			if (sourcePath.toFile().exists()) {
				fail("No TE spec should be generated when a TLC arg is \"-recover\", but " + sourcePath.toString() + " was generated.");
			}
			return;
		}

		Path destPath = Paths.get(clonedTESpecPath() + TLAConstants.Files.TLA_EXTENSION);
		try {
			Files.move(sourcePath, destPath, StandardCopyOption.REPLACE_EXISTING);
		} catch (IOException exception) {
			fail(exception.toString());
		}

		// Then we move the config file.
		sourcePath = Paths.get(originalTESpecPath() + TLAConstants.Files.CONFIG_EXTENSION);
		destPath = Paths.get(clonedTESpecPath() + TLAConstants.Files.CONFIG_EXTENSION);
		try {
			Files.move(sourcePath, destPath, StandardCopyOption.REPLACE_EXISTING);
		} catch (IOException exception) {
			fail(exception.toString());
		}

		final File outFile = new File(BASE_PATH, "test" + TLAConstants.Files.OUTPUT_EXTENSION);

		// Remove undesired args for the TE spec runner (like the `-config` argument).
	 	final int configIdx = extraArgs.indexOf("-config");
		if (configIdx >= 0) {
			extraArgs.remove(configIdx + 1);
			extraArgs.remove(configIdx);
		}
		final int simulateIdx = extraArgs.indexOf("-simulate");
		if (simulateIdx >= 0) {
			// We can have `file=` or `num=` as simulate arguments (or both), let's search for them.
			if (simulateIdx + 1 < extraArgs.size() &&
			    (extraArgs.get(simulateIdx + 1).contains("file=") || extraArgs.get(simulateIdx + 1).contains("num="))) {
				extraArgs.remove(simulateIdx + 1);
			}
			extraArgs.remove(simulateIdx);
		}

        List<String> runnerArgs = new ArrayList<String>(extraArgs);
		runnerArgs.addAll(Arrays.asList(new String[] {
			clonedTESpecPath()
		}));

		ToolIO.out.println("Running generated TE spec with args " + String.join(" ", runnerArgs));

        final TLCRunner tlcRunner = new TLCRunner(runnerArgs, outFile);

		// As we are not running in the same JVM, we ask the process to create a `.ser` file which contains
		// the raw output.
		// TLCStateInfo is one of the things that cannot be serialized, so for each `EC.TLC_STATE_PRINT2`, we get a
		// Object[] containing `stateInfo.toString()`, the state number (integer) and `stateInfo.info` (string).
		// With this we can assert the trace.
		String serFilePath = BASE_PATH + "tlc_output.ser";
		TLCRunner.JVM_ARGUMENTS.add("-DTLC_CREATE_SERIALIZED_OUTPUT_FILE=" + serFilePath);

		final int teExpectedStatus;
		if (this.expectedExitStatus == ExitStatus.VIOLATION_DEADLOCK  ||
			this.expectedExitStatus == ExitStatus.VIOLATION_ASSERT    ||
			this.expectedExitStatus == ExitStatus.ERROR               ||
			this.expectedExitStatus == ExitStatus.FAILURE_SAFETY_EVAL) {
			// Generally, for TE specs errors, the TE spec generates a exit status code of `VIOLATION_SAFETY`.
			teExpectedStatus = ExitStatus.VIOLATION_SAFETY;
		} else {
			teExpectedStatus = this.expectedExitStatus;
		}

		try {
            final int errorCode = tlcRunner.run();
            if(errorCode != teExpectedStatus) {
                fail(String.format("The output of the generated TE spec TLC run was not the expected exit status (%d), it was %d instead.", 
					teExpectedStatus, errorCode));
            }

			// DFID doesn't show names for the initial predicate or the sub-actions of the next-state relation.			
			final int dfidIdx = extraArgs.indexOf("-dfid");
			checkTESpecTraceFromSerializedFile(serFilePath, dfidIdx < 0);

		} catch (IOException exception) {
            fail(exception.getMessage());
        } 
	}

	private void checkTESpecTraceFromSerializedFile(String serFilePath, boolean canCheckInitPred) {
		// Read records from the TLC runner .ser output file.
		final Map<Integer, List<Object>> teSpecRecords;
		try {
			FileInputStream fileIn = new FileInputStream(serFilePath);
			ObjectInputStream in = new ObjectInputStream(fileIn);
			teSpecRecords = (Map<Integer, List<Object>>) in.readObject();
			in.close();
			fileIn.close();
		}
		catch (IOException i) 
		{
			i.printStackTrace();
			fail(serFilePath + " was not created");
			return;
		}
		catch (ClassNotFoundException cnfe) {
			cnfe.printStackTrace();
			fail(serFilePath + " was not created");
			return;
		}

		// Assert TE spec trace with the original one.
		List<Object> teSpecTraceOutput = teSpecRecords.get(EC.TLC_STATE_PRINT2);
		List<Object> originalTraceOutput = recorder.getRecords(EC.TLC_STATE_PRINT2);
		assertEquals(recorder.getRecords(EC.TLC_STATE_PRINT2).size(), teSpecRecords.get(EC.TLC_STATE_PRINT2).size());
		for (int i = 0; i < originalTraceOutput.size(); i++) {
			final Object[] teSpecObjs = (Object[]) teSpecTraceOutput.get(i);
			final String teSpecStateInfoStr = (String) teSpecObjs[0];
			final String info = (String) teSpecObjs[2];

			final Object[] originalObjs = (Object[]) originalTraceOutput.get(i);
			final TLCStateInfo originalStateInfo = (TLCStateInfo) originalObjs[0];				

			if (i == 0 && canCheckInitPred) {
				// The first state has to be an initial state.
				assertEquals("<Initial predicate>", info);
			} else {
				// ... all others are reachable via an action.
				//TODO: Assert actual action names.
				assertNotEquals("<Initial predicate>", info);
				assertFalse(info.startsWith("<Action"));
			}
			assertEquals(originalStateInfo.toString().trim(),
							teSpecStateInfoStr.trim()); // trimmed to remove any newlines or whitespace
			assertEquals(i+1, teSpecObjs[1]);
		}
	}
	
	@After
	public void tearDown() {
		// Also check assumption in `@After` as it does not skip
		// if `@Before` fails.
		if (isTESpec()) {
			checkTESpecAssumption();
		}		
		
		beforeTearDown();
		
		assertExitStatus();
	}
	
	protected void assertExitStatus() {
		assertEquals(expectedExitStatus, actualExitStatus);
	}
	
	protected boolean doCoverage() {
		return true;
	}
	
	/**
	 * @return True if TLC is to be called with "-deadlock".
	 */
	protected boolean checkDeadLock() {
		return false;
	}
	
	protected boolean doDump() {
		return true;
	}

	protected int doCheckpoint() {
		return 0;
	}

	/**
	 * @return The number of worker threads TLC should use.
	 */
	protected int getNumberOfThreads() {
		return 1;
	}
	
	protected void setExitStatus(final int exitStatus) {
		this.expectedExitStatus = exitStatus;
	}
	
	/**
	 * E.g. 
	 * ILiveCheck liveCheck = (ILiveCheck) getField(AbstractChecker.class, "liveCheck",
	 * 				getField(TLC.class, "instance", tlc));
	 */
	protected Object getField(Class<?> targetClass, String fieldName, Object instance) {
		try {
			Field field = targetClass.getDeclaredField(fieldName);
			field.setAccessible(true);
			return field.get(instance);
		} catch (NoSuchFieldException e) {
			e.printStackTrace();
		} catch (SecurityException e) {
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		}
		return null;
	}
}
