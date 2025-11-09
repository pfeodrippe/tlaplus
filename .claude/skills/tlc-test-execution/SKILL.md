---
name: tlc-test-execution
description: Execute TLC model-checking tests and interpret results. Use when running TLC tests via Ant, checking test status, or verifying exit codes from model checking runs.
---

# TLC Test Execution

## Instructions

1. Navigate to the tlatools directory
2. Use Ant to run the test:
   ```bash
   cd tlatools/org.lamport.tlatools
   ant -f customBuild.xml test-set -Dtest.testcases="tlc2/tool/RunTwicePersistentFlagTest.java"
   ```

3. Interpret the output:
   - `BUILD SUCCESSFUL` = test passed
   - `Tests run: 1, Failures: 0` = all assertions passed
   - Look for key checkpoints in output

## Examples

**Running the main test:**
```bash
ant -f customBuild.xml test-set -Dtest.testcases="tlc2/tool/RunTwicePersistentFlagTest.java"
```

**Expected output includes:**
- `DEMONSTRATION 1: TLCGlobals.mainChecker persists...`
- `DEMONSTRATION 2: TLCGlobals.mainChecker persists...`
- `CONFIRMATION: TLCGlobals.reset() successfully cleared...`
- `✓ TEST PASSED`

## Exit codes

| Code | Meaning | Action |
|------|---------|--------|
| 0 | Success | Model checked successfully |
| 2110 | Invariant violated | Expected for some test models |
| 2230 | Other error | Investigate test output |

## Best practices

- Run tests before making changes to verify baseline
- Check timestamps in trace exploration specs
- Look for consistent state demonstrations across runs
- Verify object identity changes between runs
