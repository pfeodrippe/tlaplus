# Operator Override Cache Persistence Bug (Issue #891)

## Problem Statement

When running multiple TLC instances in the same JVM, operator overrides (Java methods that implement TLA+ operators) are cached in the module AST and not cleared between runs. This causes the second run to use operator implementations from the first run, resulting in incorrect initial state calculations.

### Observed Symptoms

**Run 1** (with `account_SLASH_alice |-> 5` in Init):
```
State 1: <Initial predicate>
/\ main_var = [account_SLASH_alice |-> 5, ...]
/\ G__34493 = 1
/\ G__34494 = 5
```

**Reset** (after calling `TLCGlobals.reset()` and `RandomEnumerableValues.reset()`):
```
Reset complete
```

**Run 2** (spec defines `account_SLASH_alice |-> 1` in Init, but):
```
State 1: <Initial predicate>
/\ main_var = [account_SLASH_alice |-> 5, ...]    ← WRONG! Should be 1
/\ G__34493 = 3
/\ G__34494 = 5
```

The initial state from Run 2 incorrectly shows `account_SLASH_alice |-> 5` from Run 1!

## Root Cause

### Step 1: Loading Operator Overrides

When `SpecProcessor.load()` executes during TLC initialization, it scans for operator override definitions:

```java
// SpecProcessor.java (line ~618)
final String tlcOverrides = TLCBuiltInOverrides.class.getName() + File.pathSeparator
        + System.getProperty("tlc2.overrides.TLCOverrides", "tlc2.overrides.TLCOverrides");

for (String ovrde : tlcOverrides.split(File.pathSeparator)) {
    final Class<?> idx = this.tlaClass.loadClass(ovrde);
    if (idx != null && ITLCOverrides.class.isAssignableFrom(idx)) {
        // ... finds candidate methods that match TLA+ operator signatures
        
        for (Method m : candidateMethods) {
            final Evaluation evaluation = m.getAnnotation(Evaluation.class);
            if (evaluation != null) {
                final OpDefNode opDef = moduleNode.getOpDef(evaluation.definition());
                
                // ← HERE: Caches the Java method on the OpDefNode
                final Value val = new EvaluatingValue(m, evaluation.minLevel(), ...);
                opDef.getBody().setToolObject(toolId, val);
                this.defns.put(evaluation.definition(), val);
            }
        }
    }
}
```

### Step 2: Storage in Module AST

The operator override is stored using `setToolObject()`, which is defined in `SemanticNode.java`:

```java
// SemanticNode.java
private Object toolObjects[];

public final void setToolObject(int toolId, Object obj) {
    if (toolObjects == null) {
        toolObjects = new Object[toolId + 1];
    } else if (toolObjects.length <= toolId) {
        // ... resize array
    }
    toolObjects[toolId] = obj;
}
```

### Step 3: Module AST Persistence

The critical issue: **The module AST (including all OpDefNode objects with their toolObject caches) is never cleared between TLC runs.**

When `TLC.main()` or `Tool.fromSpec()` is called:
1. The module AST is parsed once (or reused from cache in some scenarios)
2. `SpecProcessor.load()` caches operator overrides in OpDefNode.toolObject[toolId]
3. After the run completes, `TLCGlobals.reset()` is called
4. **BUT**: The module AST and its cached OpDefNode.toolObject fields remain in memory
5. On the second run, the same OpDefNode objects are reused with stale cached operator implementations

### Step 4: Where Reset Fails

`TLCGlobals.reset()` (current implementation) clears:
- `mainChecker` (the Tool instance)
- `simulator`
- `metaDir`
- `numWorkers`
- Various flags

**But it does NOT clear:**
- Module AST nodes (OpDefNode, ModuleNode)
- OpDefNode.toolObject caches with operator overrides
- Any other cached AST data structures

## Solution Approaches

### Approach 1: Clear OpDefNode ToolObject Cache (Recommended)

Add a method to clear all cached toolObjects from the module AST:

```java
public class TLCGlobals {
    // In reset() method:
    
    // Clear operator override caches from module AST
    clearModuleASTToolObjectCache(TLC.toolId);
}

private static void clearModuleASTToolObjectCache(int toolId) {
    // Requires access to the parsed modules (ModuleSet or SpecProcessor)
    // Iterate through all OpDefNode objects and clear their toolObject caches
    
    for (ModuleNode module : allModules) {
        for (OpDefNode opDef : module.getOpDefs()) {
            opDef.getBody().setToolObject(toolId, null);
        }
    }
}
```

**Challenge**: Module AST is not directly accessible from TLCGlobals. We need to either:
1. Store a reference to the ModuleSet in TLCGlobals
2. Add a hook in SpecProcessor to clear caches
3. Access through the Tool instance (already cleared)

### Approach 2: Force Module Re-parsing

Ensure the module AST is always re-parsed on each run by clearing any internal caches that maintain module AST persistence.

**Challenge**: Need to identify where module AST caching occurs and disable it between runs.

### Approach 3: Separate JVM for Each Run (Workaround)

For the immediate term, users experiencing this bug should run each TLC instance in a separate JVM to avoid any cross-run state pollution.

## Implementation Plan

### Phase 1: Documentation & Awareness
- [x] Add javadoc to `TLCGlobals.reset()` explaining the operator override cache limitation
- [x] Create test case `OperatorOverrideCacheTest` that demonstrates the bug
- [ ] Document the issue in AGENTS.md and other developer docs

### Phase 2: Investigation
- [ ] Determine where ModuleNode/OpDefNode objects are stored after Tool creation
- [ ] Trace the lifecycle of OpDefNode.toolObject caches
- [ ] Identify if module AST is cached between SpecProcessor instances

### Phase 3: Fix
- [ ] Add API to access/clear module AST from reset context
- [ ] Implement clearing of OpDefNode.toolObject caches in TLCGlobals.reset()
- [ ] Add test case to `RunTwicePersistentFlagTest` that uses operator overrides

### Phase 4: Validation
- [ ] Verify two runs with different initial values show correct states
- [ ] Run full test suite to ensure no regressions
- [ ] Update documentation

## Test Cases

### OperatorOverrideCacheTest.java

Located in `test/tlc2/tool/OperatorOverrideCacheTest.java`:

Demonstrates the bug by:
1. Running a spec with `account_SLASH_alice = 5` (uses operator overrides)
2. Calling reset
3. Running a spec with `account_SLASH_alice = 1` 
4. Verifying the second run shows the correct initial value (currently fails - shows 5)

### RunTwicePersistentFlagTest.java

Should be extended to include a scenario with operator overrides.

## Related Code

- `src/tlc2/TLCGlobals.java` - Global state container (needs fix)
- `src/tlc2/tool/impl/SpecProcessor.java` - Where operator overrides are loaded and cached
- `src/tla2sany/semantic/SemanticNode.java` - Base class for AST nodes (defines toolObject cache)
- `src/tla2sany/semantic/OpDefNode.java` - Operator definition node (caches overrides)
- `src/tla2sany/semantic/ModuleNode.java` - Module node (contains OpDefNodes)

## References

- GitHub Issue #891: TLCGlobals persistence across multiple TLC runs in the same JVM
- Related: Similar issues with UniqueString intern table and RandomEnumerableValues ThreadLocals

---

**Last Updated**: November 9, 2025
