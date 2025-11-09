# AGENTS.md - Guide for AI Models and Developers

This document provides guidance for AI models (like Claude/Copilot) and developers on how to work with the TLA+ global state investigation and testing infrastructure.

## Overview

This repository contains an investigation into TLA+ issue #891: **TLCGlobals persistence across multiple TLC runs in the same JVM**. The investigation includes deterministic test cases that demonstrate the problem and validate the solution.

## Key Problem

When running multiple TLC model-checking instances in the same JVM (common in:
- Test harnesses
- CI/CD pipelines
- IDE plugins
- Batch checking tools

...global state from one run can interfere with subsequent runs unless `TLCGlobals.reset()` is explicitly called.

## For AI Models: Key Context

### Project Structure

```
tlaplus/
├── AGENTS.md (this file)
├── SKILLS.md (capabilities and task descriptions)
├── INVESTIGATION_REPORT.md (complete technical analysis)
├── tlatools/org.lamport.tlatools/
│   ├── test/tlc2/tool/
│   │   └── RunTwicePersistentFlagTest.java (main test, PASSES ✓)
│   ├── test-model/
│   │   ├── ModelCounter.tla/cfg (test model 1)
│   │   ├── ModelString.tla/cfg (test model 2)
│   │   └── ModelSequence.tla/cfg (test model 3)
│   └── src/tlc2/overrides/
│       └── PersistentFlagImpl.java (Java override for custom flags)
```

### What the Test Does

**File**: `RunTwicePersistentFlagTest.java`

The test demonstrates:
1. Run ModelCounter → `TLCGlobals.mainChecker` set to instance `@36916eb0` ← PERSISTS
2. Run ModelString → `TLCGlobals.mainChecker` set to instance `@45099dd3` ← PERSISTS (different object)
3. Call `TLCGlobals.reset()` → `TLCGlobals.mainChecker` becomes null ← CLEARS
4. Run ModelSequence → `TLCGlobals.mainChecker` set to instance `@4b013c76` ← FRESH (unique object)

### Critical Success Criteria

When working with this codebase:

- ✅ **Use different models for testing**: Never use the same model twice in a sequence test
- ✅ **Verify object identity**: Check that `TLCGlobals.mainChecker` objects differ (different memory addresses)
- ✅ **Test both before AND after reset**: Show persistence, then show reset clears it, then show fresh instance
- ✅ **Check actual exit codes**: ModelCounter returns 2110 (invariant violation), ModelString/Sequence return 0 (success)
- ✅ **Validate state changes**: Use assertions to prove state changes between checkpoints

## For Developers: Common Tasks

### Running the Test

```bash
cd tlatools/org.lamport.tlatools
ant -f customBuild.xml test-set -Dtest.testcases="tlc2/tool/RunTwicePersistentFlagTest.java"
```

**Expected output**:
```
BUILD SUCCESSFUL
testTLCGlobalsReset PASSED
```

### Adding a New Test Model

1. Create `test-model/ModelXxx.tla`:
```tla
---- MODULE ModelXxx ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 5
Inv == x < 10  \* or whatever invariant makes sense
====
```

2. Create `test-model/ModelXxx.cfg`:
```
INIT Init
NEXT Next
INVARIANT Inv
```

3. Update `RunTwicePersistentFlagTest.java` to use it:
```java
final int rX = runTLC("test-model/ModelXxx.tla");
```

**Important**: Use completely different model logic each time (different variables, different state spaces).

### Understanding Test Exit Codes

| Exit Code | Meaning | Example |
|-----------|---------|---------|
| 0 | Success - no errors | ModelString, ModelSequence |
| 2110 | Invariant violation | ModelCounter |
| 2230 | Other TLC error | Various |

### Debugging Global State

If a test fails, check:

1. **Is mainChecker null when it shouldn't be?**
   ```java
   System.out.println("mainChecker = " + TLCGlobals.mainChecker);
   System.out.println("mainChecker.getClass() = " + (TLCGlobals.mainChecker == null ? "null" : TLCGlobals.mainChecker.getClass()));
   ```

2. **Are objects the same instance (should differ)?**
   ```java
   if (checker1 == checker2) {
       System.out.println("ERROR: Same instance! " + System.identityHashCode(checker1));
   } else {
       System.out.println("OK: Different instances");
       System.out.println("  checker1: " + System.identityHashCode(checker1));
       System.out.println("  checker2: " + System.identityHashCode(checker2));
   }
   ```

3. **Is reset being called?**
   ```java
   TLCGlobals.reset();
   if (TLCGlobals.mainChecker != null) {
       throw new AssertionError("Reset failed!");
   }
   ```

## Best Practices for AI Models

### When Implementing Tests

1. **Always verify your assumptions**
   - Don't assume cleanup happens automatically
   - Run assertions after every state change
   - Check both presence and absence of state

2. **Use multiple test cases**
   - Never test the same thing twice
   - Vary inputs/models to catch edge cases
   - Test both failure and success paths

3. **Provide clear output**
   - Use descriptive `System.out.println()` for demonstrations
   - Label each checkpoint clearly
   - Show object identities (memory addresses) when proving distinctness

4. **Document what you're testing**
   - Comment each section with === SECTION NAME ===
   - Explain the expected behavior
   - State what should be asserted

### When Modifying TLC Infrastructure

1. **Know what resets what**:
   - `TLCGlobals.reset()` → clears mainChecker, simulator, metaDir, flags
   - `UniqueString.initialize()` → resets string intern table
   - `RandomEnumerableValues.reset()` → resets RNG ThreadLocals

2. **Test in isolation**:
   - Run your test in its own JVM process
   - Don't rely on other tests having run or not run

3. **Validate the complete reset sequence**:
   ```java
   TLCGlobals.reset();
   UniqueString.initialize();
   RandomEnumerableValues.reset();
   ```

## References

- **Main Test**: `RunTwicePersistentFlagTest.java`
- **Issue**: TLA+ #891 (Global state interference)
- **Technical Report**: `INVESTIGATION_REPORT.md`
- **Test Results**: `TEST_RESULTS.md`

## Quick Reference: Test Models

### ModelCounter
- **Variable**: `counter` (0..5)
- **Invariant**: `counter ≤ 3`
- **Outcome**: ❌ FAILS (invariant violated at counter=4)
- **States**: 5 distinct, depth 5

### ModelString
- **Variable**: `str` ("", "x", "xx")
- **Invariant**: `Len(str) ≤ 2`
- **Outcome**: ✅ PASSES (completes successfully)
- **States**: 3-4 distinct, depth 3

### ModelSequence
- **Variable**: `seq` (<<>>, <<1>>, <<1,2>>, <<1,2,3>>, <<1,2,3,4>>)
- **Invariant**: `Len(seq) ≤ 4`
- **Outcome**: ✅ PASSES (completes successfully)
- **States**: 5 distinct, depth 5

## Questions?

Refer to:
1. `INVESTIGATION_REPORT.md` for technical deep-dive
2. `SKILLS.md` for capability descriptions
3. Test source code for implementation details
