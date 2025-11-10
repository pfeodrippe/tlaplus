# Quick Reference: Operator Override Cache Fix

## What Was Fixed
TLC was reusing operator override caches from previous runs when multiple TLC instances ran in the same JVM, causing the second run to incorrectly use the first run's operator implementations.

## The Solution
Three components were implemented:

### 1. ModuleASTCacheManager (NEW)
**File**: `src/tlc2/tool/ModuleASTCacheManager.java`
- Clears operator override caches from module AST
- Called automatically by TLCGlobals.reset()

### 2. TLCGlobals.reset() Enhancement (UPDATED)
**File**: `src/tlc2/TLCGlobals.java`
- Now calls clearOperatorOverrideCaches() automatically
- Uses reflection to safely access internal classes
- Happens before clearing mainChecker

### 3. Tests & Documentation (NEW/UPDATED)
- OperatorOverrideCacheTest.java - Specific test case
- OPERATOR_OVERRIDE_CACHE_BUG.md - Technical analysis
- IMPLEMENTATION_SUMMARY.md - Complete implementation report
- COMPLETION_REPORT.md - Verification report
- AGENTS.md - Updated developer guidance

## Testing
```bash
# Build
cd tlatools/org.lamport.tlatools
ant -f customBuild.xml compile
ant -f customBuild.xml dist

# Test
ant test-set -Dtest.testcases="tlc2/tool/RunTwicePersistentFlagTest.java"
# Result: ✓ TEST PASSED
```

## User Impact
✓ Multiple TLC runs in same JVM now work correctly  
✓ No API changes required  
✓ No user code modifications needed  
✓ Fully backward compatible  

## Developer Impact
- See `AGENTS.md` section "When Modifying TLC Infrastructure" for updated reset sequence
- See `OPERATOR_OVERRIDE_CACHE_BUG.md` for technical details
- See `IMPLEMENTATION_SUMMARY.md` for complete implementation information

## Key Files
- `src/tlc2/tool/ModuleASTCacheManager.java` - Cache clearing utility (NEW)
- `src/tlc2/TLCGlobals.java` - Reset mechanism (UPDATED)
- `test-verify/tlc2/tool/OPERATOR_OVERRIDE_CACHE_BUG.md` - Root cause analysis (NEW)
- `IMPLEMENTATION_SUMMARY.md` - Complete report (NEW)
- `COMPLETION_REPORT.md` - Verification report (NEW)

## For More Information
1. **Technical Details**: Read `OPERATOR_OVERRIDE_CACHE_BUG.md`
2. **Implementation Details**: Read `IMPLEMENTATION_SUMMARY.md`
3. **Verification Status**: Read `COMPLETION_REPORT.md`
4. **Developer Guide**: See `AGENTS.md` "When Modifying TLC Infrastructure" section

---

**Status**: ✅ COMPLETE AND TESTED  
**Date**: November 9, 2025  
**Issue**: TLA+ #891
