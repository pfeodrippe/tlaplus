---
name: tlc-global-state-management
description: Manage TLCGlobals and persistent state across multiple TLC runs in the same JVM. Use when testing multi-run scenarios, ensuring isolation, or debugging state interference.
---

# TLC Global State Management

## Instructions

1. Understand what each reset method clears
2. Call resets in the correct sequence
3. Verify state changes after each reset
4. Check object identity to confirm fresh instances

## Complete Reset Sequence

```java
// For full isolation between TLC runs in the same JVM:

// 1. Clear core TLC globals
TLCGlobals.reset();

// 2. Reset string intern table
UniqueString.initialize();

// 3. Reset RNG ThreadLocals
RandomEnumerableValues.reset();
```

## What Each Method Clears

**TLCGlobals.reset()**
- `mainChecker` and `simulator` references
- `metaDir` (metadata directory)
- Configuration flags (coverageInterval, DFIDMax, etc.)
- `tlc2.module.TLC.OUTPUT` (output writer)

**UniqueString.initialize()**
- String intern table (`internTbl`)
- All interned unique strings

**RandomEnumerableValues.reset()**
- ThreadLocal RNG stacks
- Per-thread random state

## Verification Code

```java
// Check before run
if (TLCGlobals.mainChecker != null) {
    throw new AssertionError("Expected null before run");
}

// Capture state after run
Object checker1 = TLCGlobals.mainChecker;
System.out.println("State after run: " + checker1);

// Call reset
TLCGlobals.reset();
RandomEnumerableValues.reset();

// Verify cleared
if (TLCGlobals.mainChecker != null) {
    throw new AssertionError("Reset failed!");
}
```

## Object Identity Verification

```java
// Verify different instances (different runs)
if (checker1 == checker2) {
    System.out.println("ERROR: Same instance!");
} else {
    System.out.println("OK: Different instances");
    System.out.println("  checker1 hash: " + System.identityHashCode(checker1));
    System.out.println("  checker2 hash: " + System.identityHashCode(checker2));
}
```

## Best practices

- Always call reset sequence in order
- Verify state changes with explicit checks
- Use object identity (==) to verify fresh instances
- Print memory addresses when demonstrating distinctness
- Call reset between different test runs
- Don't assume Tool cleanup clears globals
