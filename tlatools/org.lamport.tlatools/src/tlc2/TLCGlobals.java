// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2;

import java.io.File;
import java.net.URISyntaxException;
import java.net.URL;
import java.text.DateFormat;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Enumeration;
import java.util.TimeZone;
import java.util.jar.Attributes;
import java.util.jar.Manifest;

import tlc2.tool.AbstractChecker;
import tlc2.tool.Simulator;

/**
 * Globals
 * @author Leslie Lamport
 * @author Yuan Yu
 * @author Simon Zambrovski
 * @author Markus A. Kuppe
 */
public class TLCGlobals
{

	public static final int DEFAULT_CHECKPOINT_DURATION = (30 * 60 * 1000) + 42;

	// The current version of TLC
    public static String versionOfTLC = "Version 2.20 of Day Month 20??";
    
    // The bound for set enumeration, used for pretty printing
    public static int enumBound = 2000;
    
    // The bound for the cardinality of a set
    public static int setBound = 1000000;

    // Number of concurrent workers
    private static int numWorkers = 1;
    
	/**
	 * Execute liveness checking when any of the disk graphs' size has increased
	 * exceeding the threshold (10% by default).
	 */
    public static double livenessThreshold = 0.1d;

    public static double livenessGraphSizeThreshold = 0.1d;

	/**
	 * Ratio of runtime dedicated to safety checking (80%) and liveness checking
	 * (20%). Some aspects of liveness are also checked during state insertion
	 * (see ILiveCheck#addNextState) and thus part of safety checking..
	 */
	public static double livenessRatio = 0.2d;
	
	public static String lnCheck = "default";
	
	public static boolean doLiveness() {
		return !(lnCheck.equals("final") || lnCheck.equals("seqfinal") || lnCheck.equals("off"));
	}

	public static boolean doSequentialLiveness() {
		return lnCheck.startsWith("seq");
	}

	public synchronized static void setNumWorkers(int n)
    {
        numWorkers = n;
    }

    public synchronized static int getNumWorkers()
    {
        return numWorkers;
    }

    public synchronized static void incNumWorkers(int n)
    {
        numWorkers += n;
    }
    
    /**
     * Increments the number of workers by 1
     */
    public static void incNumWorkers() {
    	incNumWorkers(1);
    }
    
    /**
     * Decrements the number of workers by 1
     */
    public static void decNumWorkers() {
    	incNumWorkers(-1);
    }

    // The main model checker object (null if simulator non-null)
    public static AbstractChecker mainChecker = null;
    
    // The main simulator object (null if mainChecker non-null)
    public static Simulator simulator = null;

    // Char to indent nested coverage information.
	public static final char coverageIndent = '|';
    
    // Enable collecting coverage information
    public static int coverageInterval = -1;

    public static final boolean isCoverageEnabled() {
    	return coverageInterval >= 0;
    }
    
    // Depth for depth-first iterative deepening
    public static int DFIDMax = -1;

    // Continue running even when invariant is violated
    public static boolean continuation = false;

    // Prints only the state difference in state traces
    public static boolean printDiffsOnly = false;

    // Suppress warnings report if true
    public static boolean warn = true;

    // The time interval to report progress (in milliseconds)
    // max prevents div-by-zero if users passes 0.
	public static final int progressInterval = Math
			.max(Math.abs(Integer.getInteger(TLC.class.getName() + ".progressInterval", 60)), 1) * 1000;

    // The time interval to checkpoint. (in milliseconds)
	public static long chkptDuration = Integer.getInteger(
			TLCGlobals.class.getName() + ".chkpt", DEFAULT_CHECKPOINT_DURATION);
    
	// MAK 08.2012: centralized checkpoint code and added disabling and
	// externally forced checkpoints
    private static boolean forceChkpt = false;
    public static void forceChkpt() {
    	forceChkpt = true;
    }
    private static long lastChkpt = System.currentTimeMillis();

	public static boolean chkptExplicitlyEnabled() {
		// Assumption is that a user will always select a different value.
		return chkptDuration > 0 && chkptDuration != DEFAULT_CHECKPOINT_DURATION;
	}

	/**
	 * IMPORTANT NOTE: The method is unsynchronized. It is the caller's
	 * responsibility to ensure that only a single thread calls this method.
	 * 
	 * @return true iff a checkpoint should be created next time possible
	 */
    public static boolean doCheckPoint() {
    	// 1. checkpoint forced externally (e.g. JMX)
    	if (forceChkpt) {
    		forceChkpt = false;
    		return true;
    	}
    	
    	// 2. user has disabled checkpoints
    	if (chkptDuration == 0) {
    		return false;
    	}
    	
    	// 3. time between checkpoints is up?
        long now = System.currentTimeMillis();
        if (now - lastChkpt >= TLCGlobals.chkptDuration) {
        	lastChkpt = now;
        	return true;
        }
        return false;
    }

    // The meta data root.
    public static final String metaRoot = "states";
    public static String metaDir = null;

    // The flag to control if VIEW is applied when printing out states.
    public static boolean useView = false;

    // The flag to control if gzip is applied to Value input/output stream.
    public static boolean useGZIP = false;

    // debugging field
    public static boolean debug = false;

    // format messages easy for parsing
    public static boolean tool = false;

	public static boolean isValidSetSize(final int bound) {
		if (bound < 1) {
			return false;
		}
		return true;
	}
	
	public static boolean expand = true;
	
	public static String getRevision() {
		return getManifestValue("X-Git-ShortRevision");
	}
	
	public static String getRevisionOrDev() {
		return TLCGlobals.getRevision() == null ? "development" : TLCGlobals.getRevision();
	}
	
	public static Date getBuildDate() {
		try {
			final String manifestValue = getManifestValue("Build-TimeStamp");
			if (manifestValue == null) {
				return new Date();
			}
			final DateFormat df = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss.S'Z'");
			df.setTimeZone(TimeZone.getTimeZone("UTC"));
			// TLC's Build-TimeStamp in the jar's Manifest is format according to ISO 8601
			// (https://en.m.wikipedia.org/wiki/ISO_8601)
			return df.parse(manifestValue);
		} catch (NullPointerException | ParseException e) {
			// There is no manifest or the manifest does not contain a build time stamp, in
			// which case we return the current, syntactically equivalent time stamp.
			// This is usually the case when running TLC from an IDE or the 'test' target of
			// the Ant custombuild.xml file. In other words, this occurs during TLC development.
			// However, regular usage should not take this branch.
			// https://en.m.wikipedia.org/wiki/ISO_8601
			return new Date();
		}
	}

	public static int getSCMCommits() {
		try {
			return Integer.parseInt(getManifestValue("X-Git-Commits-Count"));
		} catch (NullPointerException | NumberFormatException nfe) {
			// Not mapping to -1 so that at the level of TLA+ it is \in Nat.
			return 0;
		}
	}
	
	private static String getManifestValue(final String key) {
		try {
			final Enumeration<URL> resources = TLCGlobals.class.getClassLoader().getResources("META-INF/MANIFEST.MF");
			while (resources.hasMoreElements()) {
				final Manifest manifest = new Manifest(resources.nextElement().openStream());
				final Attributes attributes = manifest.getMainAttributes();
				if("TLA+ Tools".equals(attributes.getValue("Implementation-Title"))) {
					if(attributes.getValue(key) != null) {
						return attributes.getValue(key);
					} else {
						return null;
					}
				}
			}
		} catch (Exception ignore) {
		}
		return null;
	}
	
	public static String getInstallLocation() {
		try {
			return new File(TLC.class.getProtectionDomain().getCodeSource().getLocation().toURI()).getPath();
		} catch (URISyntaxException e) {
			return "unknown";
		}
	}
	
	public static final class Coverage {
		
		private static final int coverage = Integer.getInteger(TLCGlobals.class.getName() + ".coverage", 0);

		public static boolean isVariableEnabled() {
			if (isCoverageEnabled()) {
				return true;
			}
			return (coverage & 2) > 0;
		}

		public static boolean isActionEnabled() {
			if (isCoverageEnabled()) {
				return true;
			}
			return (coverage & 1) > 0;
		}

		public static boolean isEnabled() {
			if (isCoverageEnabled()) {
				return true;
			}
			return coverage > 0;
		}
	}
	
	/**
	 * Reset TLC globals to their initial state to allow running TLC multiple
	 * times in the same JVM. This addresses issue #891.
	 * 
	 * WARNING: This method should only be called when NO TLC instances are
	 * running. Calling this while TLC is running will cause undefined behavior.
	 * 
	 * This method resets:
	 * - TLCGlobals fields (mainChecker, simulator, metaDir, etc.)
	 * - Operator override caches in module AST (OpDefNode.toolObject)
	 * - Context static state (semantic analysis global context via Context.reInit())
	 * - RandomEnumerableValues ThreadLocal state (random number generators)
	 * 
	 * NOTE: This method intentionally does NOT clear:
	 * - UniqueString.internTbl (string intern table) - Clearing this breaks subsequent parsing
	 * - User-defined static fields that cache state
	 * - Java system properties
	 * 
	 * @see <a href="https://github.com/tlaplus/tlaplus/issues/891">Issue #891</a>
	 */
	public static synchronized void reset() {
		// First attempt to clear operator override caches from previous run
		// This must be done before clearing mainChecker
		clearOperatorOverrideCaches();
		
		// Reset checker references
		mainChecker = null;
		simulator = null;
		
		// Reset metadata directory
		metaDir = null;
		
		// Reset number of workers to default
		numWorkers = 1;
		
		// Reset liveness parameters to defaults
		livenessThreshold = 0.1d;
		livenessGraphSizeThreshold = 0.1d;
		livenessRatio = 0.2d;
		lnCheck = "default";
		
		// Reset coverage
		coverageInterval = -1;
		
		// Reset DFID
		DFIDMax = -1;
		
		// Reset flags and behavior settings
		continuation = false;
		printDiffsOnly = false;
		warn = true;
		useView = false;
		useGZIP = false;
		debug = false;
		tool = false;
		expand = true;
		
		// Reset checkpoint state
		forceChkpt = false;
		lastChkpt = System.currentTimeMillis();
		
		// Reset TLC module OUTPUT
		// Note: We close it first in case it's open
		if (tlc2.module.TLC.OUTPUT != null) {
			try {
				tlc2.module.TLC.OUTPUT.flush();
				tlc2.module.TLC.OUTPUT.close();
			} catch (Exception e) {
				// Ignore errors during cleanup
			}
			tlc2.module.TLC.OUTPUT = null;
		}
		
		// Reset semantic analysis global state - critical for multiple TLC runs
		// Context maintains a static initialContext that must be re-initialized
		// This resets the global symbol table context for parsing
		try {
			tla2sany.semantic.Context.reInit();
		} catch (Exception e) {
			throw new RuntimeException("Failed to reset Context: " + e.getMessage(), e);
		}
		
		// Reset random number generator ThreadLocals
		// This should happen AFTER Context.reInit() to avoid interference
		try {
			tlc2.value.RandomEnumerableValues.reset();
		} catch (Exception e) {
			throw new RuntimeException("Failed to reset RandomEnumerableValues: " + e.getMessage(), e);
		}
		
		// NOTE: We do NOT reset UniqueString.initialize() automatically here because:
		// - It clears the ENTIRE intern table
		// - This breaks subsequent module parsing in the same JVM session
		// - The string intern table is shared globally and clearing it causes parser failures
		// - Users/applications that absolutely need this should call UniqueString.initialize() 
		//   themselves when appropriate (ONLY at the start of a completely new independent session)
		
		// NOTE: Fields that are NOT reset:
		// - versionOfTLC: read-only version string
		// - enumBound, setBound: user configuration values
		// - chkptDuration: set from system property, persists across runs
		// - progressInterval: final value computed from system property
		// - Coverage.coverage: static final, set from system property
	}

	/**
	 * Performs a more aggressive reset than {@link #reset()} by additionally clearing
	 * various auxiliary global/static caches/subsystems that can accumulate state
	 * across multiple TLC runs inside the same JVM. This should be used with care;
	 * if external tooling depends on specific caches persisting, call plain {@code reset()} instead.
	 *
	 * Deep reset adds:
	 *  - PlusCal parser/translator static scratch state cleared (ParseAlgorithm, PcalTranslate)
	 *  - ValueInputStream.customValues cleared (user registered value readers)
	 *  - SimpUtil/ModelValue/JVM debug helpers reset to pristine defaults
	 *  - FrontEnd tool id counter reset (idCnt) to zero to keep toolObject index space compact
	 *
	 * It intentionally still does NOT clear UniqueString's intern table (same reason as in reset()).
	 *
	 * If any of the reflection-based cleanup steps fail, a RuntimeException is thrown to
	 * surface the defect early rather than silently ignoring it.
	 */
	public static synchronized void deepReset() {
		// First perform the regular reset (includes operator override cache clearing).
		reset();
		// Then clear additional global state.
		clearPlusCalState();
		clearPcalTokenizeState();
		clearValueInputStreamCustomValues();
		clearSimpUtilState();
		clearModelValueState();
		clearTLCDebuggerOverride();
		clearTLCRunnerState();
		resetFrontEndToolIdCounter();
	}

	private static void clearPlusCalState() {
		// Clear ParseAlgorithm static scratch fields and re-initialize built-in symbols.
		try {
			final Class<?> parseAlg = Class.forName("pcal.ParseAlgorithm");
			for (String fieldName : new String[]{"charReader","currentProcedure"}) {
				final java.lang.reflect.Field f = parseAlg.getDeclaredField(fieldName);
				f.setAccessible(true);
				f.set(null, null);
			}
			for (String fieldName : new String[]{"plusLabels","minusLabels","proceduresCalled","addedLabels","addedLabelsLocs","procedures"}) {
				final java.lang.reflect.Field f = parseAlg.getDeclaredField(fieldName);
				f.setAccessible(true);
				f.set(null, new java.util.Vector<>());
			}
			for (String fieldName : new String[]{"allLabels"}) {
				final java.lang.reflect.Field f = parseAlg.getDeclaredField(fieldName);
				f.setAccessible(true);
				f.set(null, new java.util.Hashtable<>());
			}
			for (String fieldName : new String[]{"gotoUsed","gotoDoneUsed","omitPC","omitStutteringWhenDone","hasDefaultInitialization","pSyntax","cSyntax","hasLabel"}) {
				final java.lang.reflect.Field f = parseAlg.getDeclaredField(fieldName);
				f.setAccessible(true);
				f.setBoolean(null, false);
			}
			for (String fieldName : new String[]{"nextLabelNum","lastTokCol","lastTokLine"}) {
				final java.lang.reflect.Field f = parseAlg.getDeclaredField(fieldName);
				f.setAccessible(true);
				f.setInt(null, 0);
			}
			for (String fieldName : new String[]{"getLabelLocation"}) {
				final java.lang.reflect.Field f = parseAlg.getDeclaredField(fieldName);
				f.setAccessible(true);
				f.set(null, null);
			}
			// Re-initialize AST singletons and parameter defaults
			final Class<?> pcalParams = Class.forName("pcal.PcalParams");
			pcalParams.getMethod("resetParams").invoke(null);
			final Class<?> ast = Class.forName("pcal.AST");
			ast.getMethod("ASTInit").invoke(null);
			// Re-initialize built-in symbol tables (idempotent)
			final Class<?> pcalBuiltIns = Class.forName("pcal.PcalBuiltInSymbols");
			final java.lang.reflect.Method init = pcalBuiltIns.getMethod("Initialize");
			init.invoke(null);
			// Clear PcalTranslate static state if present.
			try {
				final Class<?> pcalTranslate = Class.forName("pcal.PcalTranslate");
				for (String fName : new String[]{"st","currentProcedure"}) {
					final java.lang.reflect.Field f = pcalTranslate.getDeclaredField(fName);
					f.setAccessible(true);
					f.set(null, null);
				}
			} catch (ClassNotFoundException ignored) {
				// Optional component absent.
			}
		} catch (Exception e) {
			throw new RuntimeException("Failed to clear PlusCal state: " + e.getMessage(), e);
		}
	}

	private static void clearPcalTokenizeState() {
		try {
			final Class<?> tokenize = Class.forName("pcal.Tokenize");
			for (String fieldName : new String[]{"Delimiter"}) {
				final java.lang.reflect.Field f = tokenize.getDeclaredField(fieldName);
				f.setAccessible(true);
				f.set(null, null);
			}
			for (String fieldName : new String[]{"DelimiterLine","DelimiterCol"}) {
				final java.lang.reflect.Field f = tokenize.getDeclaredField(fieldName);
				f.setAccessible(true);
				f.setInt(null, 0);
			}
			final java.lang.reflect.Field readerField = tokenize.getDeclaredField("reader");
			readerField.setAccessible(true);
			readerField.set(null, null);
		} catch (ClassNotFoundException e) {
			// Optional component absent; ignore.
		} catch (Exception e) {
			throw new RuntimeException("Failed to clear PlusCal tokenize state: " + e.getMessage(), e);
		}
	}

	private static void clearValueInputStreamCustomValues() {
		try {
			final Class<?> vis = Class.forName("tlc2.value.ValueInputStream");
			final java.lang.reflect.Field f = vis.getDeclaredField("customValues");
			f.setAccessible(true);
			@SuppressWarnings("unchecked") final java.util.Map<Byte,?> map = (java.util.Map<Byte,?>) f.get(null);
			if (map != null) map.clear();
		} catch (Exception e) {
			throw new RuntimeException("Failed to clear ValueInputStream customValues: " + e.getMessage(), e);
		}
	}

	private static void clearSimpUtilState() {
		try {
			final Class<?> simpUtil = Class.forName("tlc2.util.SimpUtil");
			final java.lang.reflect.Field defns = simpUtil.getDeclaredField("defns");
			defns.setAccessible(true);
			defns.set(null, new java.util.Hashtable<>());
		} catch (ClassNotFoundException e) {
			// Older builds might not have this helper.
		} catch (Exception e) {
			throw new RuntimeException("Failed to clear SimpUtil state: " + e.getMessage(), e);
		}
	}

	private static void clearModelValueState() {
		try {
			final Class<?> modelValue = Class.forName("tlc2.value.impl.ModelValue");
			final java.lang.reflect.Field mvs = modelValue.getDeclaredField("mvs");
			mvs.setAccessible(true);
			mvs.set(null, null);
		} catch (ClassNotFoundException e) {
			// Component absent; ignore.
		} catch (Exception e) {
			throw new RuntimeException("Failed to clear ModelValue state: " + e.getMessage(), e);
		}
	}

	private static void clearTLCDebuggerOverride() {
		try {
			final Class<?> debugger = Class.forName("tlc2.debug.TLCDebugger");
			final java.lang.reflect.Field override = debugger.getDeclaredField("OVERRIDE");
			override.setAccessible(true);
			override.set(null, null);
		} catch (ClassNotFoundException | NoSuchFieldException e) {
			// Debugger or override hook not present; ignore.
		} catch (Exception e) {
			throw new RuntimeException("Failed to clear TLCDebugger override: " + e.getMessage(), e);
		}
	}

	private static void clearTLCRunnerState() {
		try {
			final Class<?> tlcRunner = Class.forName("tlc2.TLCRunner");
			final java.lang.reflect.Field jvmArgs = tlcRunner.getDeclaredField("JVM_ARGUMENTS");
			jvmArgs.setAccessible(true);
			jvmArgs.set(null, null);
		} catch (ClassNotFoundException e) {
			// Class not available; ignore.
		} catch (Exception e) {
			throw new RuntimeException("Failed to clear TLCRunner state: " + e.getMessage(), e);
		}
	}

	private static void resetFrontEndToolIdCounter() {
		try {
			final Class<?> frontEnd = Class.forName("tla2sany.semantic.FrontEnd");
			final java.lang.reflect.Field idCnt = frontEnd.getDeclaredField("idCnt");
			idCnt.setAccessible(true);
			idCnt.setInt(null, 0);
		} catch (Exception e) {
			// Non-critical; leave counter untouched if inaccessible.
		}
	}
	
	/**
	 * Clears operator override caches from the module AST of any previously run checkers.
	 * 
	 * This is called automatically by reset() to address issue #891.
	 * Operator overrides are Java methods loaded from ITLCOverrides implementations
	 * and cached in OpDefNode.toolObject fields. These caches must be cleared between
	 * TLC runs to ensure clean re-initialization.
	 * 
	 * This method is safe to call even if no previous checker exists.
	 */
	private static void clearOperatorOverrideCaches() {
		if (mainChecker == null) {
			// No previous checker to clear caches from
			return;
		}
		
		try {
			// Access the ITool from the checker, then get SpecProcessor
			final Object tool = mainChecker.getClass().getField("tool").get(mainChecker);
			if (tool == null) {
				return;
			}
			
			// Get the SpecProcessor from ITool
			final Object specProcessor = tool.getClass().getMethod("getSpecProcessor").invoke(tool);
			
			if (specProcessor == null) {
				return;
			}
			
			// Get the SpecObj from SpecProcessor
			final Class<?> specProcessorClass = specProcessor.getClass();
			final java.lang.reflect.Method getSpecObjMethod = specProcessorClass.getMethod("getSpecObj");
			final Object specObj = getSpecObjMethod.invoke(specProcessor);
			
			if (specObj == null) {
				return;
			}
			
			// Get ExternalModuleTable from SpecObj
			final Class<?> specObjClass = specObj.getClass();
			final java.lang.reflect.Method getExternalModuleTableMethod = specObjClass.getMethod("getExternalModuleTable");
			final Object moduleTable = getExternalModuleTableMethod.invoke(specObj);
			
			if (moduleTable == null) {
				return;
			}
			
			// Get the toolId from SpecProcessor (it's a private field)
			final java.lang.reflect.Field toolIdField = specProcessorClass.getDeclaredField("toolId");
			toolIdField.setAccessible(true);
			final int toolId = toolIdField.getInt(specProcessor);
			
			// Call ModuleASTCacheManager.clearModuleASTCache(moduleTable, toolId)
			// Use reflection to avoid hard dependency
			final Class<?> cacheManagerClass = Class.forName("tlc2.tool.ModuleASTCacheManager");
			final java.lang.reflect.Method clearCacheMethod = cacheManagerClass.getMethod(
				"clearModuleASTCache", 
				Class.forName("tla2sany.semantic.ExternalModuleTable"),
				int.class
			);
			clearCacheMethod.invoke(null, moduleTable, toolId);
		} catch (final ClassNotFoundException e) {
			// ModuleASTCacheManager not available
			throw new RuntimeException("Failed to clear operator override caches: " + e.getMessage(), e);
		} catch (final Exception e) {
			// Propagate any other exceptions
			throw new RuntimeException("Failed to clear operator override caches: " + e.getMessage(), e);
		}
	}
}

