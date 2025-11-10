---
name: tlc-multi-run-test-design
description: Design tests that verify state isolation and global state management across multiple TLC runs. Use when creating comprehensive test sequences, testing reset mechanisms, or demonstrating state persistence.
---

# TLC Multi-Run Test Design

## Instructions

1. Plan test sequence with different models
2. Capture state at each checkpoint
3. Verify state changes between runs
4. Assert object identity differences
5. Confirm reset effectiveness

## Test Pattern: Sequential Multi-Model Test

This pattern demonstrates both persistence and reset:

```java
@Test
public void testStateManagement() throws Exception {
    // Phase 1: Verify initial state
    assertNull(TLCGlobals.mainChecker);

    // Phase 2: First model run
    final int r1 = runTLC("test-model/ModelA.tla");
    if (r1 == 0) {
        throw new AssertionError("ModelA should fail");
    }
    Object checker1 = TLCGlobals.mainChecker;
    assertNotNull(checker1);
    System.out.println("DEMONSTRATION 1: " + checker1);

    // Phase 3: Second model run (DIFFERENT model)
    final int r2 = runTLC("test-model/ModelB.tla");
    if (r2 != 0) {
        throw new AssertionError("ModelB should pass");
    }
    Object checker2 = TLCGlobals.mainChecker;
    assertNotNull(checker2);
    if (checker1 == checker2) {
        throw new AssertionError("Should be different objects!");
    }
    System.out.println("DEMONSTRATION 2: " + checker2);
    System.out.println("VERIFICATION: Different objects");

    // Phase 4: Reset
    TLCGlobals.reset();
    RandomEnumerableValues.reset();
    if (TLCGlobals.mainChecker != null) {
        throw new AssertionError("Reset failed!");
    }
    System.out.println("CONFIRMATION: Reset successful");

    // Phase 5: Third model run (fresh instance expected)
    final int r3 = runTLC("test-model/ModelC.tla");
    if (r3 != 0) {
        throw new AssertionError("ModelC should pass");
    }
    Object checker3 = TLCGlobals.mainChecker;
    assertNotNull(checker3);
    if (checker1 == checker3 || checker2 == checker3) {
        throw new AssertionError("Should be new instance!");
    }
    System.out.println("DEMONSTRATION 3: " + checker3);
}
```

## Key Assertion Points

| Checkpoint | Assertion | Proves |
|------------|-----------|--------|
| After Run 1 | `checker1 != null` | State persists |
| After Run 2 | `checker1 != checker2` | Different instances |
| After Reset | `mainChecker == null` | Reset works |
| After Run 3 | `checker3 != checker1 && checker3 != checker2` | Fresh instance |

## Examples

**Real test: RunTwicePersistentFlagTest.java**
- Run 1: ModelCounter (fails at invariant)
- Run 2: ModelString (passes)
- Reset called
- Run 3: ModelSequence (passes)
- All assertions verified

## Best practices

- Use DIFFERENT models for each run (never repeat)
- Vary model complexity and behavior
- Test both pass and fail scenarios
- Capture and display object identities
- Add clear checkpoint messages
- Verify exit codes match expectations
- Don't assume state carries over
- Always reset between major test phases
