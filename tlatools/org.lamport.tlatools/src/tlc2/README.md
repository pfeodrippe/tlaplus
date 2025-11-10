# TLC - The TLA⁺ Model Checker

## Table of Contents

- [Overview](#overview)
- [What Does TLC Do?](#what-does-tlc-do)
- [Architecture](#architecture)
- [Core Components](#core-components)
- [Known Issues and Unexpected Behaviors](#known-issues-and-unexpected-behaviors)
- [Roadmap: Potential Improvements](#roadmap-potential-improvements)
- [Development Notes](#development-notes)

## Overview

The `tlc2` package contains **TLC** (Temporal Logic Checker), the heart of TLA⁺'s model checking capabilities. TLC is an explicit-state model checker that exhaustively explores the state space of TLA⁺ specifications to verify safety properties (invariants) and liveness properties (temporal logic formulas).

TLC was originally developed by Yuan Yu at Compaq Systems Research Center and has been continuously enhanced since 2003. It's designed to handle industrial-scale specifications and can leverage distributed computing for massive state spaces.

## What Does TLC Do?

### Core Capabilities

1. **Safety Checking**: Verifies that invariants hold in all reachable states
   - Checks user-defined invariants
   - Detects deadlocks (when enabled)
   - Validates type correctness
   - Ensures state constraints are satisfied

2. **Liveness Checking**: Verifies that temporal properties eventually hold
   - Checks fairness conditions
   - Detects livelocks and infinite stuttering
   - Uses Strongly Connected Component (SCC) analysis via Tarjan's algorithm
   - Can checkpoint liveness graphs for long-running checks

3. **State Space Exploration**: Systematically explores all reachable states
   - Breadth-first search (BFS) by default
   - Depth-first iterative deepening (DFID) for memory-constrained scenarios
   - Parallel exploration using multiple worker threads
   - Distributed model checking across multiple machines
   - Simulation mode for probabilistic exploration of large/infinite state spaces

4. **Counterexample Generation**: When properties are violated, TLC produces:
   - Complete error traces showing the path to the violation
   - State-by-state differences
   - Action labels showing which transitions were taken
   - Full variable assignments at each step

5. **Performance Optimizations**:
   - **Fingerprinting**: 64-bit fingerprints for efficient state comparison
   - **Disk-based storage**: Handles state spaces larger than RAM
   - **Checkpointing**: Save and resume long-running model checks
   - **Coverage tracking**: Identifies unexplored parts of the specification
   - **Symmetry reduction**: Reduces state space for symmetric specifications (safety only)

### Operational Modes

- **Model Checking Mode** (`ModelChecker.java`): Exhaustive state space exploration
- **Simulation Mode** (`Simulator.java`): Random walk through state space for rapid feedback
- **DFID Mode** (`DFIDModelChecker.java`): Depth-first iterative deepening for bounded memory
- **Debug Mode**: Integration with DAP (Debug Adapter Protocol) for interactive debugging

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                          TLC Architecture                           │
└─────────────────────────────────────────────────────────────────────┘

                         ┌──────────────┐
                         │   TLC.java   │
                         │ Entry Point  │
                         └──────┬───────┘
                                │
                  ┌─────────────┴─────────────┐
                  │                           │
        ┌─────────▼──────────┐    ┌──────────▼────────────┐
        │   ModelChecker     │    │     Simulator         │
        │  (BFS Checking)    │    │  (Random Walk)        │
        └─────────┬──────────┘    └──────────┬────────────┘
                  │                           │
                  │                ┌──────────▼────────────┐
                  │                │ DFIDModelChecker      │
                  │                │ (Bounded Memory)      │
                  │                └───────────────────────┘
                  │
      ┌───────────┴────────────┐
      │                        │
┌─────▼─────┐          ┌───────▼────────┐
│  Workers  │          │  State Queue   │
│ (Parallel │          │ (BFS/DFID/Mem) │
│  Threads) │          └───────┬────────┘
└─────┬─────┘                  │
      │              ┌─────────┴──────────┐
      │              │                    │
      │        ┌─────▼──────┐      ┌─────▼──────┐
      │        │   FPSet    │      │   Trace    │
      │        │(Fingerprint│      │   (Error   │
      │        │   Storage) │      │  Tracking) │
      │        └─────┬──────┘      └────────────┘
      │              │
      └──────────────┴────────┐
                              │
                    ┌─────────▼──────────┐
                    │    Tool/ITool      │
                    │  (TLA+ Evaluator)  │
                    └─────────┬──────────┘
                              │
                    ┌─────────▼──────────┐
                    │   Value System     │
                    │  (State Storage)   │
                    └────────────────────┘


┌──────────────────────────────────────────────────────────────────────┐
│                     Component Interactions                           │
└──────────────────────────────────────────────────────────────────────┘

  Worker Thread Loop:
  ┌──────────────────────────────────────────────────────────────┐
  │  1. Dequeue state from StateQueue                            │
  │  2. Generate successors via Tool.getNextStates()             │
  │  3. For each successor:                                      │
  │     a. Compute 64-bit fingerprint                            │
  │     b. Check if seen in FPSet                                │
  │     c. If new: check invariants, add to queue & trace        │
  │     d. If liveness: add to LiveCheck's state graph           │
  │  4. Check for deadlock (if enabled)                          │
  │  5. Update statistics (states generated, queue depth, etc.)  │
  │  6. Repeat until queue is empty or error found               │
  └──────────────────────────────────────────────────────────────┘

  Periodic Operations (AbstractChecker.doPeriodicWork()):
  ┌──────────────────────────────────────────────────────────────┐
  │  • Suspend all workers                                       │
  │  • Run liveness checking (if enabled)                        │
  │  • Create checkpoint (FPSet + Queue + Trace)                 │
  │  • Print progress statistics                                 │
  │  • Resume workers                                            │
  └──────────────────────────────────────────────────────────────┘
```

### Directory Structure

```
tlc2/
├── TLC.java                    # Main entry point, CLI parsing
├── TLCGlobals.java            # Global configuration constants
├── REPL.java                  # Interactive REPL
├── Simulator.java             # Simulation mode
│
├── tool/                      # Core model checking engine
│   ├── ModelChecker.java      # BFS model checker
│   ├── DFIDModelChecker.java  # Depth-first iterative deepening
│   ├── AbstractChecker.java   # Common checker functionality
│   ├── Worker.java            # Worker thread for parallel exploration
│   ├── SimulationWorker.java  # Worker for simulation mode
│   ├── ITool.java             # Interface to TLA+ evaluator
│   ├── TLCState.java          # Abstract state representation
│   ├── TLCStateMut.java       # Mutable state (main implementation)
│   ├── TLCStateFun.java       # Functional/immutable state
│   ├── Action.java            # Represents next-state actions
│   │
│   ├── impl/                  # TLA+ specification evaluator
│   │   ├── Tool.java          # Main TLA+ evaluation engine
│   │   └── FastTool.java      # Optimized variant
│   │
│   ├── fp/                    # Fingerprint set implementations
│   │   ├── FPSet.java         # Abstract fingerprint set
│   │   ├── MemFPSet.java      # In-memory implementation
│   │   ├── DiskFPSet.java     # Disk-backed implementation
│   │   └── OffHeapDiskFPSet.java # Off-heap + disk hybrid
│   │
│   ├── queue/                 # State queue implementations
│   │   ├── IStateQueue.java   # Queue interface
│   │   ├── StateQueue.java    # Abstract base
│   │   ├── MemStateQueue.java # In-memory queue
│   │   └── DiskStateQueue.java # Disk-backed queue
│   │
│   ├── liveness/              # Liveness checking
│   │   ├── LiveCheck.java     # Main liveness checker
│   │   ├── LiveWorker.java    # Worker for liveness checking
│   │   └── Liveness.java      # Liveness property representation
│   │
│   ├── coverage/              # Coverage tracking
│   │   ├── CostModel.java     # Action coverage model
│   │   └── CostModelCreator.java
│   │
│   ├── distributed/           # Distributed model checking
│   │   ├── TLCServer.java     # Coordinator
│   │   └── TLCWorker.java     # Remote worker
│   │
│   └── management/            # JMX monitoring
│       └── TLCStatisticsMXBean.java
│
├── value/                     # TLA+ value system
│   ├── IValue.java            # Value interface
│   ├── impl/                  # Value implementations
│   │   ├── IntValue.java
│   │   ├── StringValue.java
│   │   ├── SetEnumValue.java
│   │   ├── TupleValue.java
│   │   └── RecordValue.java
│   └── ValueInputStream.java  # Serialization
│
├── module/                    # TLA+ standard modules
│   ├── Naturals.java
│   ├── Sequences.java
│   ├── FiniteSets.java
│   └── TLC.java               # TLC built-in operators
│
├── output/                    # Error reporting and output
│   ├── MP.java                # Message printer
│   ├── EC.java                # Error codes
│   └── Messages.properties    # Error messages
│
├── debug/                     # Debugger support (DAP)
│   ├── TLCDebugger.java
│   └── TLCDebuggerExpression.java
│
├── overrides/                 # Module overrides for performance
├── pprint/                    # Pretty printing
└── util/                      # Utilities
    ├── FP64.java              # 64-bit fingerprint computation
    └── StateWriter.java       # State output
```

## Core Components

### ModelChecker.java

The main breadth-first search model checker. Key responsibilities:

- **Initial state generation**: Evaluates Init predicate to find all initial states
- **State space exploration**: BFS traversal using worker threads
- **Invariant checking**: Validates all invariants on every state
- **Liveness checking**: Periodic SCC detection on state graph
- **Checkpoint/recovery**: Save and restore model checking progress

Key data structures:
- `FPSet theFPSet`: Stores fingerprints of all seen states (disk or memory)
- `IStateQueue theStateQueue`: Queue of unexplored states
- `ConcurrentTLCTrace trace`: Error trace reconstruction
- `Worker[] workers`: Parallel worker threads

### Worker.java

Worker thread that performs the actual state exploration:

```java
// Simplified worker loop
while (true) {
    TLCState curState = queue.dequeue();
    if (curState == null) break; // Done
    
    // Generate all successor states
    for (TLCState successor : tool.getNextStates(curState)) {
        long fp = successor.fingerPrint();
        
        if (!fpSet.contains(fp)) {
            // New state discovered
            checkInvariants(successor);
            queue.enqueue(successor);
            trace.write(curState, successor);
        }
    }
}
```

### FPSet (Fingerprint Set)

Tracks which states have been visited using 64-bit fingerprints:

- **MemFPSet**: Hash table in RAM (fastest, limited capacity)
- **DiskFPSet**: Memory-mapped files (scales to billions of states)
- **OffHeapDiskFPSet**: Off-heap memory + disk (best performance/capacity trade-off)

Fingerprints are computed using a custom hash function that distributes state fingerprints uniformly across the 64-bit space.

### Tool/ITool

The bridge between TLC and the TLA+ specification:

- Evaluates TLA+ expressions in the context of states
- Generates initial states from Init predicate
- Computes successors from Next action
- Checks invariants, type correctness, and properties
- Handles module instantiation and operator definitions

### LiveCheck

Implements liveness checking using SCC detection:

1. Build directed graph from explored states (using `LiveWorker`)
2. Run Tarjan's algorithm to find strongly connected components
3. Check each SCC for accepting states (where fairness conditions hold)
4. If accepting SCC found with reachable deadlock, liveness violated

**Note**: Currently sequential - a major performance bottleneck for large state spaces.

## Known Issues and Unexpected Behaviors

### Architectural Limitations

1. **Global Mutable State Everywhere** (**PARTIALLY FIXED**): TLC heavily uses global variables (`TLCGlobals`), making it difficult to:
   - Run multiple model checks in the same JVM
   - Use TLC as a library
   - Write unit tests that don't interfere with each other
   - **Specific Issue**: [#891](https://github.com/tlaplus/tlaplus/issues/891) tracks the effort to remove all static global variables
   - **Key Problem Globals**:
     - `TLCGlobals.mainChecker` and `TLCGlobals.simulator` - set during model checking and never reset
     - `TLCGlobals.metaDir` - path to metadata directory
     - `UniqueString.internTbl` - string interning table that accumulates strings across runs
     - `TLCGlobals.lastChkpt` - checkpoint timestamp
     - `tlc2.module.TLC.OUTPUT` - output writer that needs cleanup
     - `RandomEnumerableValues` - ThreadLocal random number generators
     - Various flags: `coverageInterval`, `DFIDMax`, `continuation`, etc.
   - **Impact**: Running TLC twice in the same JVM without using classloader isolation fails with unpredictable errors
   - **SOLUTION** (as of 2025-11-09): Call these methods to reset global state between TLC runs:
     ```java
     TLCGlobals.reset();          // Reset global flags and references
     UniqueString.initialize();    // Reset string intern table
     RandomEnumerableValues.reset(); // Reset random number generators
     ```
   - **Workaround** (legacy): Run TLC in separate processes, or use `IsolatedTestCaseRunner` which loads TLC in isolated classloaders
   - **Test**: See `test/tlc2/tool/RunTwiceTest.java` for a demonstration that TLC can now run twice in the same JVM

2. **Sequential Liveness Checking**: Tarjan's SCC algorithm runs single-threaded, creating a bottleneck
   - Liveness checking can take longer than safety checking
   - Only one core utilized even with 64+ cores available
   - Partial workaround: Reduce liveness checking frequency with `-lncheck`

3. **Memory-Mapped File Limits**: DiskFPSet uses memory-mapped files which can hit OS limits
   - Linux: May need to increase `vm.max_map_count`
   - Windows: Can exhaust virtual address space on 32-bit JVMs
   - **Workaround**: Use `-fp` to tune FPSet size parameters

### Performance Quirks

4. **Fingerprint Collision Risk**: Theoretically possible (though never observed)
   - TLC uses 64-bit fingerprints
   - Collision probability: ~1 in 2^32 for 4 billion states (birthday paradox)
   - **Impact**: Could cause TLC to miss states (unsound)
   - **Mitigation**: Use `-fpbits` to increase fingerprint bits in critical checks

5. **Lock Contention in FPSet**: With many workers, FPSet locking can bottleneck
   - OffHeapDiskFPSet uses lock-free algorithms for better scaling
   - MemFPSet has coarse-grained locking
   - **Tune**: Adjust number of workers with `-workers`

6. **State Queue Thrashing**: Queue operations trigger disk I/O when memory fills
   - Dramatically slows down exploration
   - **Tune**: Use `-checkpoint` to increase memory allocated to queue

7. **Trace File Fragmentation**: Each worker writes to separate trace file
   - Reconstructing error traces requires merging fragments
   - Can be slow for deep traces (10,000+ states)

### Semantic Gotchas

8. **Invariant Checking Order**: Invariants checked in definition order, not optimal order
   - First invariant violation found may not be the "simplest"
   - **Workaround**: Put most likely violations first

9. **Action Fairness Interactions**: Strong and weak fairness can interact unexpectedly
   - Multiple fairness conditions can create unintended liveness guarantees
   - **Debug**: Use `-liveness` to see fairness graph

10. **Simulation Mode Limitations**:
    - Ignores `ASSUME` statements (doesn't validate preconditions)
    - Random exploration may miss corner cases
    - Coverage metrics less meaningful
    - Liveness checking uses different (less thorough) algorithm

11. **DFID Memory Accounting**: DFID mode's memory estimates can be off
    - May restart at lower depth than necessary
    - Or exceed memory before restarting
    - **Tune**: Adjust `-depth` manually for better control

### Error Reporting

12. **Cryptic "null" Errors**: Some code paths print "null" instead of meaningful errors
    - Usually indicates unsupported language construct
    - Or internal assertion failure
    - **Debug**: Run with `-debug` for stack traces

13. **Incomplete Error Traces**: In distributed mode, error traces can be incomplete
    - Workers don't have full trace information
    - Coordinator must reconstruct from fingerprints
    - Can fail if checkpoint data is inconsistent

14. **Deadlock vs Termination**: TLC treats "no successors" as deadlock
    - Specs with terminal states need `\/ UNCHANGED vars` in Next
    - Or use `-deadlock` to disable deadlock checking

### Distributed Mode Issues

15. **Network Partition Handling**: Distributed TLC doesn't handle network failures gracefully
    - Workers can get "stuck" waiting for coordinator
    - No automatic retry or failover
    - **Workaround**: Use `-cleanup` to restart failed workers

16. **Clock Skew**: Distributed workers rely on coordinator's clock
    - Checkpointing can fail if clocks are out of sync
    - **Fix**: Ensure NTP is running on all machines

17. **RMI Registry Conflicts**: Multiple TLC instances on same machine can conflict
    - RMI registry port (1099) is shared
    - **Workaround**: Use `-port` to specify different port

### Concurrency Bugs

18. **Race Conditions in Checkpointing**: Rare race between checkpointing and worker threads
    - Can result in corrupted checkpoint
    - **Symptom**: "Cannot recover from checkpoint" error
    - **Workaround**: Increase checkpoint interval with `-checkpoint`

19. **Worker Synchronization Deadlocks**: Under high contention, workers can deadlock
    - Especially with many workers (64+) and small state spaces
    - **Symptom**: TLC appears "stuck" with workers waiting
    - **Workaround**: Reduce number of workers

## Roadmap: Potential Improvements

### Performance Improvements

#### Low-Hanging Fruit (Easy - Moderate Effort)

- **Optimize Fingerprint Computation** (Easy)
  - **Description**: Profile and optimize `FP64.java` hot paths
  - **Impact**: High (called billions of times)
  - **Risk**: Low
  - **Effort**: 1-2 weeks
  - **Skills**: Java, profiling tools (JProfiler, async-profiler)

- **Replace Custom Collections** (Easy)
  - **Description**: Replace `tlc2.util.Vect` and others with standard `java.util` collections
  - **Impact**: Moderate (smaller binary, less maintenance)
  - **Risk**: Medium (subtle behavior differences)
  - **Effort**: 2-3 weeks
  - **Skills**: Java, refactoring

- **Cache Frequently-Computed Values** (Moderate)
  - **Description**: Memoize expensive evaluations in `Tool.java`
  - **Impact**: Moderate to High
  - **Risk**: Low (pure optimization)
  - **Effort**: 2-4 weeks
  - **Skills**: Java, caching strategies

- **Improve FPSet Concurrency** (Moderate)
  - **Description**: Reduce lock contention in MemFPSet using concurrent data structures
  - **Impact**: High (better multi-core scaling)
  - **Risk**: Medium
  - **Effort**: 3-4 weeks
  - **Skills**: Java concurrency, lock-free algorithms

#### Medium-Hanging Fruit (Significant Effort)

- **Concurrent Strongly Connected Components** (High Difficulty)
  - **Description**: Replace Tarjan's sequential SCC with parallel algorithm
  - **Impact**: Revolutionary (enables multi-core liveness checking)
  - **Risk**: High (requires formal verification of correctness)
  - **Effort**: 3-6 months
  - **Skills**: Concurrent algorithms, formal methods, TLA+
  - **Reference**: [Multi-Core SCC Decomposition](https://github.com/utwente-fmt/ppopp16)
  - **Note**: Ongoing work - see main repo contributions.md

- **Incremental State Space Exploration** (High Difficulty)
  - **Description**: Cache exploration results, reuse when spec changes slightly
  - **Impact**: Very High (speeds up iterative development)
  - **Risk**: High (complex invalidation logic)
  - **Effort**: 4-6 months
  - **Skills**: Caching, incremental computation, TLA+

- **Adaptive Worker Scaling** (Moderate)
  - **Description**: Dynamically adjust number of workers based on queue depth and contention
  - **Impact**: High (better resource utilization)
  - **Risk**: Medium
  - **Effort**: 4-6 weeks
  - **Skills**: Java, performance tuning, heuristics

- **Better State Queue Data Structures** (Moderate)
  - **Description**: Optimize queue for cache locality and reduce allocations
  - **Impact**: High
  - **Risk**: Medium
  - **Effort**: 6-8 weeks
  - **Skills**: Data structures, cache-aware algorithms

#### Not-So-Low-Hanging Fruit (Major Undertaking)

- **Symbolic Model Checking Integration** (Very High Difficulty)
  - **Description**: Hybrid explicit + symbolic (BDD/SAT) state space exploration
  - **Impact**: Revolutionary (enables verification of infinite state spaces)
  - **Risk**: Very High
  - **Effort**: 12-18 months (PhD-level)
  - **Skills**: BDDs, SAT/SMT solvers, symbolic algorithms, TLA+

- **GPU-Accelerated Fingerprinting** (High Difficulty)
  - **Description**: Offload fingerprint computation to GPU
  - **Impact**: High (potentially 10-100x speedup for fingerprinting)
  - **Risk**: Very High (major architectural change)
  - **Effort**: 6-12 months
  - **Skills**: CUDA/OpenCL, GPU programming, Java JNI

- **Distributed Liveness Checking** (Very High Difficulty)
  - **Description**: Distribute SCC computation across multiple machines
  - **Impact**: Very High (enables liveness checking on huge state spaces)
  - **Risk**: Very High
  - **Effort**: 12+ months
  - **Skills**: Distributed algorithms, graph partitioning, formal methods

### Security Improvements

#### Low-Hanging Fruit (Easy)

- **Input Validation** (Easy)
  - **Description**: Validate all command-line arguments, file paths, and user inputs
  - **Impact**: High (prevents injection attacks)
  - **Risk**: Very Low
  - **Effort**: 1-2 weeks
  - **Skills**: Java, security best practices

- **Dependency Scanning** (Easy)
  - **Description**: Integrate OWASP Dependency-Check into CI/CD
  - **Impact**: High (catches vulnerable dependencies)
  - **Risk**: Very Low
  - **Effort**: 1 week
  - **Skills**: Maven, CI/CD

- **Security-Focused Static Analysis** (Easy)
  - **Description**: Add SpotBugs security audit rules
  - **Impact**: Moderate
  - **Risk**: Very Low
  - **Effort**: 1 week
  - **Skills**: Static analysis tools

#### Medium-Hanging Fruit (Moderate)

- **Sandbox Model Checking** (Moderate)
  - **Description**: Run TLC in sandboxed environment with restricted I/O and network
  - **Impact**: High (prevents malicious specs from harming system)
  - **Risk**: Medium (may break legitimate use cases)
  - **Effort**: 4-8 weeks
  - **Skills**: Java Security Manager, sandboxing

- **Cryptographic Module Signing** (Moderate)
  - **Description**: Sign and verify TLA+ modules to ensure authenticity
  - **Impact**: Moderate to High
  - **Risk**: Medium
  - **Effort**: 6-8 weeks
  - **Skills**: Java, cryptography, PKI

### Architectural Improvements

#### Low-Hanging Fruit (Easy)

- **Improve Documentation** (Easy)
  - **Description**: Document key algorithms, data structures, and design decisions
  - **Impact**: High (easier onboarding)
  - **Risk**: Very Low
  - **Effort**: 4-6 weeks
  - **Skills**: Technical writing

- **Increase Test Coverage** (Easy)
  - **Description**: Add unit tests for core components (FPSet, StateQueue, Worker)
  - **Impact**: High (catches regressions)
  - **Risk**: Very Low
  - **Effort**: Ongoing
  - **Skills**: Java, JUnit, test design

- **Extract Utility Classes** (Easy)
  - **Description**: Identify and extract reusable utilities to reduce duplication
  - **Impact**: Moderate
  - **Risk**: Low
  - **Effort**: 2-4 weeks
  - **Skills**: Java, refactoring

#### Medium-Hanging Fruit (Moderate)

- **Improve Error Messages** (Moderate)
  - **Description**: Replace cryptic errors (including "null") with actionable guidance
  - **Impact**: Very High (better user experience)
  - **Risk**: Low
  - **Effort**: 4-8 weeks
  - **Skills**: Java, UX, technical writing

- **Runtime API for TLC** (Moderate)
  - **Description**: Replace CLI with REST/gRPC API for control and metrics
  - **Impact**: High (enables monitoring, cloud integration)
  - **Risk**: Medium
  - **Effort**: 8-12 weeks
  - **Skills**: API design, REST/gRPC, Java

- **Modularize TLC Codebase** (Moderate to High)
  - **Description**: Break TLC into well-defined modules with clear interfaces
  - **Impact**: High (improves maintainability)
  - **Risk**: Medium to High
  - **Effort**: 3-6 months
  - **Skills**: Software architecture, refactoring

- **Plugin Architecture** (High)
  - **Description**: Allow users to write plugins for custom state space reductions, storage backends, etc.
  - **Impact**: High
  - **Risk**: High
  - **Effort**: 4-6 months
  - **Skills**: Java, plugin architectures, API design

#### Not-So-Low-Hanging Fruit (Major Undertaking)

- **Remove Global Mutable State** (Very High Difficulty)
  - **Description**: Refactor to eliminate `TLCGlobals` and other global variables
  - **Impact**: Very High (enables TLC as library, concurrent model checks)
  - **Risk**: Very High (subtle soundness bugs possible)
  - **Effort**: 12-18 months
  - **Skills**: Java, architecture, extensive testing
  - **Note**: MUST be done incrementally with extreme care. Previous attempts introduced soundness bugs.

- **Persistent State Space Storage** (High Difficulty)
  - **Description**: Store state space in database for querying and analysis
  - **Impact**: High (enables post-hoc analysis, state space visualization)
  - **Risk**: High
  - **Effort**: 6-12 months
  - **Skills**: Databases, storage engines, Java

### Tooling & User Experience

#### Low-Hanging Fruit (Easy)

- **Better Progress Reporting** (Easy)
  - **Description**: More informative progress messages (ETA, state space statistics)
  - **Impact**: Moderate
  - **Risk**: Very Low
  - **Effort**: 2-3 weeks
  - **Skills**: Java, statistics

- **JSON Output Format** (Easy)
  - **Description**: Add `-output json` for machine-readable output
  - **Impact**: Moderate (enables tooling)
  - **Risk**: Very Low
  - **Effort**: 2-3 weeks
  - **Skills**: Java, JSON

- **State Space Visualization** (Easy to Moderate)
  - **Description**: Generate GraphViz/D3.js visualizations of small state spaces
  - **Impact**: High (aids understanding)
  - **Risk**: Low
  - **Effort**: 3-4 weeks
  - **Skills**: GraphViz, web technologies

#### Medium-Hanging Fruit (Moderate)

- **Interactive Debugger** (High Difficulty)
  - **Description**: DAP-based debugger for stepping through state exploration
  - **Impact**: Very High (revolutionary debugging experience)
  - **Risk**: Medium
  - **Effort**: 4-6 months
  - **Skills**: DAP, Java, debugger protocols
  - **Note**: Basic DAP support exists in `tlc2/debug/`

- **Real-Time Metrics Dashboard** (Moderate)
  - **Description**: Web UI showing state space growth, worker utilization, coverage
  - **Impact**: High
  - **Risk**: Low
  - **Effort**: 6-8 weeks
  - **Skills**: Web development, Java, metrics

- **Checkpoint Management UI** (Moderate)
  - **Description**: Tool for inspecting, comparing, and managing checkpoints
  - **Impact**: Moderate
  - **Risk**: Low
  - **Effort**: 4-6 weeks
  - **Skills**: Java, UI design

### Priority Recommendations

**Start Here (Highest ROI):**
1. Improve error messages (high impact, low risk)
2. Add comprehensive unit tests (prevents regressions)
3. Optimize fingerprint computation (immediate perf win)
4. Better documentation (helps all contributors)
5. JSON output format (enables tooling ecosystem)

**High Impact, Reasonable Effort:**
1. Concurrent SCC detection (game-changer for liveness)
2. Runtime API for TLC (enables monitoring, cloud integration)
3. Improved FPSet concurrency (better multi-core scaling)
4. Interactive debugger (revolutionary user experience)
5. State space visualization (aids understanding)

**Moonshots (High Risk, High Reward):**
1. Remove global mutable state (enables library usage)
2. Symbolic model checking (handles infinite state spaces)
3. Distributed liveness checking (scales liveness to massive state spaces)
4. GPU acceleration (massive speedup potential)
5. Persistent state space storage (enables analysis tooling)

## Development Notes

### Building & Testing

See the parent repository's [DEVELOPING.md](../../../DEVELOPING.md) for build instructions.

To run tests for TLC specifically:
```bash
cd tlatools/org.lamport.tlatools
ant -f customBuild.xml test-set -Dtest.testcases="tlc2/**/*Test.java"
```

### Code Style

- Follow existing style (mixture of styles due to multi-decade development)
- Use meaningful variable names (avoid single-letter names except in loops)
- Document non-obvious algorithms and design decisions
- Add tests for new features and bug fixes

### Key Invariants to Maintain

1. **Fingerprint Uniqueness**: FPSet must never lose fingerprints
2. **Trace Consistency**: Error traces must be reconstructable from stored fingerprints
3. **Worker Synchronization**: Workers must coordinate on queue empty condition
4. **Checkpoint Atomicity**: Checkpoints must be all-or-nothing
5. **Soundness**: TLC must explore all reachable states (unless using simulation/symmetry)

### Performance Testing

When making performance changes:
1. Use specifications from `test-model/` directory
2. Benchmark before and after (use `-tool` for timing stats)
3. Test with varying numbers of workers (1, 2, 4, 8, 16, 32)
4. Test both safety and liveness checking
5. Profile with async-profiler or JProfiler

### Common Pitfalls

- **Don't modify fingerprints after putting in FPSet**: Fingerprints are immutable once computed
- **Don't skip invariant checks**: Even if "obvious", check all invariants
- **Don't assume worker execution order**: Workers run concurrently and non-deterministically
- **Don't use `System.out.println`**: Use `MP.printMessage()` or `ToolIO`
- **Don't introduce new global state**: We're trying to reduce it, not add more!

### Useful Debugging Flags

- `-debug`: Enable debug logging (verbose)
- `-tool`: Print detailed timing statistics
- `-coverage 1`: Print action coverage after each state
- `-dump dot,colorize,actionlabels filename.dot`: Dump state graph to GraphViz
- `-workers 1`: Single-threaded (easier to debug)

### Resources

- [TLA+ Website](http://lamport.azurewebsites.net/tla/tla.html) - Main TLA+ documentation
- [TLC Paper](http://lamport.azurewebsites.net/tla/tlc.html) - Original TLC design document
- [Specifying Systems](http://lamport.azurewebsites.net/tla/book.html) - TLA+ book by Leslie Lamport
- [TLA+ Video Course](http://lamport.azurewebsites.net/video/videos.html) - Video tutorials
- [TLA+ Examples](https://github.com/tlaplus/Examples) - Specification examples

---

**Maintainers**: TLA+ Foundation  
**License**: MIT  
**Original Author**: Yuan Yu (Compaq SRC / Microsoft Research)  
**Major Contributors**: Leslie Lamport, Simon Zambrovski, Markus Kuppe, and many others
