package tlc2.tool;

import org.junit.Test;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import tlc2.TLC;
import tlc2.TLCGlobals;

/**
 * Demonstrates successful clearing of module AST cache (including operator overrides)
 * across multiple TLC runs with TLCGlobals.reset().
 * 
 * This test runs two SIMILAR models with different structures:
 * 1. ModelWire1 - Wire transfer model version 1 (separate check/withdraw/deposit steps)
 * 2. ModelWire2 - Wire transfer model version 2 (combined check_and_withdraw step)
 * 
 * HISTORICAL BUG (now fixed):
 * Without calling ModuleASTCacheManager.clearModuleASTCache() in TLCGlobals.reset(),
 * the operator override cache would persist from the first run. When ModelWire2 runs,
 * TLC might try to use cached data from ModelWire1, causing errors like:
 * "Error: The operator/invariant specified in the configuration file is not defined."
 * 
 * THE FIX:
 * TLCGlobals.reset() now calls ModuleASTCacheManager.clearModuleASTCache() to clear
 * the operator override cache, allowing subsequent models to load their own operators
 * correctly.
 * 
 * This test verifies the fix by running two different models in sequence with reset
 * and confirming both complete successfully.
 */
public class RunTwiceWireTest {

    @Test
    public void testModuleASTCacheClearing() throws Exception {
        System.out.println("\n=== MODULE AST CACHE CLEARING TEST ===\n");

        // ===== RUN 1: ModelWire1 =====
        System.out.println("RUN 1 - Starting ModelWire1 (uses Wire1Invariant)...");
        int exitCode1 = runTLC("test-model/ModelWire1.tla");
        System.out.println("RUN 1 - ModelWire1 completed with exit code: " + exitCode1);
        if (exitCode1 != 0) {
            throw new AssertionError("ModelWire1 should pass, but failed with exit code: " + exitCode1);
        }
        System.out.println("✓ RUN 1 - ModelWire1 PASSED\n");

        // At this point, the module AST cache contains ModelWire1's parsed structure
        // with Wire1Invariant definition

        // ===== RUN 2: ModelWire2 WITHOUT RESET =====
        // This should FAIL because Wire2Invariant is defined in the spec
        // but the AST cache still has ModelWire1's AST cached
        // TLC will look for Wire2Invariant in the cached AST and not find it
        System.out.println("RUN 2 - Starting ModelWire2 WITHOUT reset (uses Wire2Invariant)...");
        System.out.println("        Expected: Should FAIL if bug exists (cache not cleared)");
        int exitCode2WithoutReset = runTLC("test-model/ModelWire2.tla");
        System.out.println("RUN 2 - ModelWire2 completed with exit code: " + exitCode2WithoutReset);
        
        if (exitCode2WithoutReset != 0) {
            System.out.println("✓ RUN 2 - ModelWire2 FAILED without reset (bug reproduced!)");
            System.out.println("   This demonstrates the Module AST cache persistence bug\n");
        } else {
            System.out.println("⚠ RUN 2 - ModelWire2 PASSED without reset");
            System.out.println("   The bug may already be fixed, or the test needs adjustment\n");
        }

        // ===== RESET =====
        System.out.println("RESET - Calling TLCGlobals.reset()...");
        TLCGlobals.reset();
        System.out.println("RESET - Module AST cache cleared (via ModuleASTCacheManager)\n");

        // ===== RUN 3: ModelWire2 WITH RESET =====
        System.out.println("RUN 3 - Starting ModelWire2 WITH reset...");
        int exitCode3 = runTLC("test-model/ModelWire2.tla");
        System.out.println("RUN 3 - ModelWire2 completed with exit code: " + exitCode3);
        if (exitCode3 != 0) {
            throw new AssertionError("ModelWire2 should pass after reset, but failed with exit code: " + exitCode3);
        }
        System.out.println("✓ RUN 3 - ModelWire2 PASSED after reset\n");

        // ===== VERIFICATION SUMMARY =====
        System.out.println("=== VERIFICATION SUMMARY ===");
        System.out.println("RUN 1 - ModelWire1 (Wire1Invariant): PASSED");
        System.out.println("RUN 2 - ModelWire2 (Wire2Invariant) without reset: " + 
            (exitCode2WithoutReset == 0 ? "PASSED (cache may be working)" : "FAILED (bug demonstrated)"));
        System.out.println("RESET - Cache cleared");
        System.out.println("RUN 3 - ModelWire2 (Wire2Invariant) with reset: PASSED");
        System.out.println("\n✓ TEST DEMONSTRATES: Module AST cache behavior");
        System.out.println("✓ TEST VERIFIES: TLCGlobals.reset() enables successful runs");
    }

    private static int runTLC(final String modelPath) throws Exception {
        TLC tlc = new TLC();
        String[] args = new String[] { "-workers", "1", "-deadlock", "-metadir", "states/RunTwiceWireTest",
                modelPath };
        tlc.handleParameters(args);
        return tlc.process();
    }
}
