---
name: tlc-debugging-state-issues
description: Debug global state interference and identify state persistence problems. Use when tests fail unexpectedly, state isn't cleared after reset, or multiple runs interfere with each other.
---

# TLC Debugging State Issues

## Instructions

1. Identify the symptom
2. Add diagnostic output
3. Check specific state components
4. Verify reset sequence
5. Confirm fix

## Diagnostic Techniques

### State Snapshots

Print complete state at key points:

```java
System.out.println("=== STATE CHECKPOINT ===");
System.out.println("mainChecker: " + TLCGlobals.mainChecker);
System.out.println("simulator: " + TLCGlobals.simulator);
System.out.println("metaDir: " + TLCGlobals.metaDir);
System.out.println("========================");
```

### Object Tracking

Track objects across multiple runs:

```java
List<String> checkers = new ArrayList<>();
checkers.add("Before run 1: " + TLCGlobals.mainChecker);

runTLC("test-model/ModelA.tla");
checkers.add("After run 1: " + TLCGlobals.mainChecker);

runTLC("test-model/ModelB.tla");
checkers.add("After run 2: " + TLCGlobals.mainChecker);

for (String s : checkers) {
    System.out.println(s);
}
```

### Reset Verification

Check that reset actually clears state:

```java
System.out.println("Before reset: " + TLCGlobals.mainChecker);

TLCGlobals.reset();
RandomEnumerableValues.reset();

System.out.println("After reset: " + TLCGlobals.mainChecker);

if (TLCGlobals.mainChecker != null) {
    System.err.println("ERROR: Reset failed!");
    throw new AssertionError("mainChecker not cleared!");
}
```

### Memory Address Inspection

Verify fresh instances:

```java
Object obj1 = TLCGlobals.mainChecker;
System.out.println("obj1 address: " + System.identityHashCode(obj1));

// ... reset ...

Object obj2 = TLCGlobals.mainChecker;
System.out.println("obj2 address: " + System.identityHashCode(obj2));

if (System.identityHashCode(obj1) == System.identityHashCode(obj2)) {
    System.out.println("ERROR: Same memory location!");
} else {
    System.out.println("OK: Different memory locations");
}
```

## Common Issues and Solutions

### Issue: mainChecker not null after reset

**Diagnosis:**
```java
if (TLCGlobals.mainChecker != null) {
    throw new AssertionError("TLCGlobals.reset() failed!");
}
```

**Solution:**
- Verify `TLCGlobals.reset()` was called
- Check `RandomEnumerableValues.reset()` also called
- Ensure no other code is setting mainChecker

### Issue: Same object after different runs

**Diagnosis:**
```java
if (checker1 == checker2) {
    System.out.println("ERROR: Same instance!");
    System.out.println("Hash: " + System.identityHashCode(checker1));
}
```

**Solution:**
- Verify you're using DIFFERENT models
- Check models actually execute (run TLC successfully)
- Ensure no reset between runs in this scenario

### Issue: State from previous test interferes

**Diagnosis:**
```java
// At start of test
if (TLCGlobals.mainChecker != null) {
    throw new AssertionError("State leaked from previous test!");
}
```

**Solution:**
- Add reset at beginning of test
- Call complete reset sequence
- Check test execution order

## Debugging Workflow

1. **Identify symptom**: Does test fail? How?
2. **Add snapshots**: Print state at checkpoints
3. **Check components**: Is it mainChecker? metaDir?
4. **Verify reset**: Did reset() actually run?
5. **Inspect memory**: Use identityHashCode()
6. **Fix and retest**: Verify diagnostic proves fix

## Best practices

- Always print object identity hashes
- Use try-catch to capture before cleanup
- Label each checkpoint clearly
- Compare before/after states
- Verify object inequality with ==, not equals()
- Don't trust toString() for object identity
