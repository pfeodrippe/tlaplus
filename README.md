# TLA⁺ Tools and Toolbox

[![CI](https://github.com/tlaplus/tlaplus/workflows/CI/badge.svg)](https://github.com/tlaplus/tlaplus/actions?query=workflow%3ACI)
[![Sonatype Nexus (Snapshots)](https://img.shields.io/nexus/s/org.lamport/tla2tools?server=https%3A%2F%2Foss.sonatype.org)](https://oss.sonatype.org/content/repositories/snapshots/org/lamport/tla2tools/)

## Table of Contents

- [Overview](#overview)
- [What Does This Project Do?](#what-does-this-project-do)
- [Project Architecture](#project-architecture)
- [Use](#use)
- [Known Issues and Unexpected Behaviors](#known-issues-and-unexpected-behaviors)
- [Developing & Contributing](#developing--contributing)
- [Roadmap: Potential Improvements](#roadmap-potential-improvements)
- [License & Copyright](#license--copyright)

## Overview

This repository hosts the core TLA⁺ command line interface (CLI) Tools and the Toolbox integrated development environment (IDE).
Its development is managed by the [TLA⁺ Foundation](https://foundation.tlapl.us/).
See http://tlapl.us for more information about TLA⁺ itself.
For the TLA⁺ proof manager, see http://proofs.tlapl.us.

Versioned releases can be found on the [Releases](https://github.com/tlaplus/tlaplus/releases) page.
Currently, every commit to the master branch is built & uploaded to the [1.8.0 Clarke pre-release](https://github.com/tlaplus/tlaplus/releases/tag/v1.8.0).
If you want the latest fixes & features you can use that pre-release.
If you want to consume the TLA⁺ tools as a Java dependency in your software project, Maven packages are periodically published to [oss.sonatype.org](https://oss.sonatype.org/content/repositories/snapshots/org/lamport/tla2tools/).

## What Does This Project Do?

TLA⁺ is a formal specification language for designing, modeling, and verifying concurrent and distributed systems. This repository provides the essential tools to work with TLA⁺ specifications:

### Core Tools (tla2tools.jar)

The TLA⁺ Tools JAR contains multiple command-line utilities:

- **TLC Model Checker** (`tlc2.TLC`): The heart of TLA⁺'s verification capabilities. TLC exhaustively explores the state space of your specification to verify safety properties (invariants) and liveness properties (temporal logic). It can detect deadlocks, property violations, and provide counterexamples. TLC supports both breadth-first and depth-first search modes, distributed model checking across multiple machines, and simulation mode for extremely large state spaces.

- **SANY Parser** (`tla2sany.SANY`): The TLA⁺ syntax analyzer and semantic checker. SANY parses TLA⁺ specifications, validates syntax, performs semantic analysis, resolves module dependencies, and generates an abstract syntax tree (AST) used by other tools. It's the first stage in any TLA⁺ workflow.

- **PlusCal Translator** (`pcal.trans`): PlusCal is an algorithm language that transpiles to TLA⁺. This translator converts PlusCal algorithms (written in a more imperative, pseudocode-like style) into TLA⁺ specifications. This allows engineers familiar with traditional programming to describe systems in a more familiar notation while still leveraging TLA⁺'s formal verification capabilities.

- **TLA⁺ to LaTeX Converter** (`tla2tex.TLA`): Converts TLA⁺ specifications into beautifully typeset LaTeX documents. This is invaluable for producing publication-quality documentation, papers, and presentations of your formal specifications.

- **TLA⁺ REPL** (`tlc2.REPL`): An interactive read-eval-print-loop for evaluating TLA⁺ expressions and exploring specifications interactively.

### TLA⁺ Toolbox IDE

The Toolbox is a full-featured IDE built on Eclipse RCP that provides:

- **Syntax Highlighting & Editing**: Context-aware editing with syntax highlighting, error detection, and navigation features
- **Module Management**: Organize specifications into modules with automatic dependency resolution
- **Model Checking Interface**: Graphical interface to configure and run TLC, set constants, define invariants, and analyze results
- **Error Visualization**: Step-by-step error traces with state visualization for debugging counterexamples
- **PlusCal Integration**: Automatic translation and synchronization between PlusCal and TLA⁺
- **Cloud TLC**: Integration with cloud providers (AWS, Azure) to run large-scale model checking on distributed infrastructure
- **Proof Manager Integration**: Support for TLAPS (TLA⁺ Proof System) for mechanical theorem proving

## Project Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     TLA⁺ Ecosystem                              │
└─────────────────────────────────────────────────────────────────┘
                              │
                ┌─────────────┴─────────────┐
                │                           │
    ┌───────────▼──────────┐    ┌──────────▼────────────┐
    │   TLA⁺ Tools CLI     │    │  TLA⁺ Toolbox IDE     │
    │   (tla2tools.jar)    │    │  (Eclipse RCP)        │
    └──────────┬───────────┘    └──────────┬────────────┘
               │                           │
      ┌────────┴────────┐         ┌────────┴────────┐
      │                 │         │                 │
┌─────▼──────┐  ┌──────▼──────┐  ┌──────▼──────┐  │
│   SANY     │  │    TLC      │  │   PlusCal   │  │
│  Parser    │  │   Model     │  │ Translator  │  │
│            │  │  Checker    │  │             │  │
└─────┬──────┘  └──────┬──────┘  └─────────────┘  │
      │                │                           │
      │         ┌──────┴──────┐                    │
      │         │             │                    │
      │  ┌──────▼──────┐ ┌────▼────────┐          │
      │  │ State Space │ │  Liveness   │          │
      │  │ Exploration │ │   Checking  │          │
      │  └─────────────┘ └─────────────┘          │
      │                                            │
      └────────────────┬───────────────────────────┘
                       │
             ┌─────────▼──────────┐
             │  Semantic Engine   │
             │  - Type Checking   │
             │  - Symbol Table    │
             │  - AST Generation  │
             └────────────────────┘

Directory Structure:
├── tlatools/org.lamport.tlatools/  ← Core TLA⁺ command-line tools
│   ├── src/
│   │   ├── tla2sany/               ← Parser and semantic analyzer
│   │   ├── tlc2/                   ← TLC model checker engine
│   │   ├── pcal/                   ← PlusCal to TLA⁺ translator
│   │   └── tla2tex/                ← LaTeX pretty-printer
│   ├── test/                       ← Unit tests
│   └── test-model/                 ← Test specifications
│
└── toolbox/                        ← Eclipse-based IDE
    ├── org.lamport.tla.toolbox/    ← Core Toolbox framework
    ├── org.lamport.tla.toolbox.editor.basic/  ← Editor components
    ├── org.lamport.tla.toolbox.tool.tlc/      ← TLC integration
    └── org.lamport.tla.toolbox.tool.prover/   ← TLAPS integration
```

## Use

The TLA⁺ tools require Java 11+ to run.
The `tla2tools.jar` file contains multiple TLA⁺ tools.
They can be used as follows:
```bash
java -cp tla2tools.jar tla2sany.SANY -help  # The TLA⁺ parser
java -cp tla2tools.jar tlc2.TLC -help       # The TLA⁺ model checker
java -cp tla2tools.jar tlc2.REPL            # Enter the TLA⁺ REPL
java -cp tla2tools.jar pcal.trans -help     # The PlusCal-to-TLA⁺ translator
java -cp tla2tools.jar tla2tex.TLA -help    # The TLA⁺-to-LaTeX translator
```
If you add `tla2tools.jar` to your [`CLASSPATH`](https://docs.oracle.com/javase/tutorial/essential/environment/paths.html) environment variable then you can skip the `-cp tla2tools.jar` parameter.
Running `java -jar tla2tools.jar` is aliased to `java -cp tla2tools.jar tlc2.TLC`.

## Known Issues and Unexpected Behaviors

While TLA⁺ is a powerful tool for formal verification, there are several gotchas and unexpected behaviors that users should be aware of:

### Language & Semantic Gotchas

1. **`Seq(S)` is Unenumerable**: Using `Seq(S)` in specifications can cause TLC to fail with an "unenumerable" error because `Seq(S)` represents the infinite set of all finite sequences over `S`. Instead, bound sequences explicitly (e.g., `{s \in Seq(S) : Len(s) <= MaxLen}`).

2. **INVARIANT vs PROPERTY Confusion**: Switching from `INVARIANT I` to `PROPERTY I` requires updating the definition. An invariant `I` is a state predicate, but a property `I` needs to be a temporal formula (usually `[]I`). Failing to update this causes confusing errors.

3. **Infix Operators Don't Always Work with Unicode**: Some infix operator transformations fail when using Unicode characters, particularly in PlusCal translation contexts.

4. **NULL Pointer Errors**: TLC occasionally reports "null" as an error message instead of something meaningful, particularly when using unsupported language constructs or edge cases in model evaluation.

5. **Symmetry Breaks Liveness Checking**: TLC's liveness checking can incorrectly succeed or fail when symmetry reduction is enabled. Symmetry reduction currently only works reliably for safety properties.

6. **Simulation Mode Ignores ASSUMPTIONS**: When running in simulation mode, TLC does not verify ASSUMPTIONS, which can lead to unexpected behavior if your model relies on assumptions being validated.

### Tooling & Build Quirks

7. **Ant and Eclipse Build Conflicts**: Running Ant builds from the command line while Eclipse is open can cause Eclipse to report phantom compilation errors. Always run Ant from within Eclipse, or close Eclipse when using command-line builds.

8. **Java Version Sensitivity for Toolbox Builds**: Building the Toolbox with Java versions newer than 11 often causes build failures. Stick to Java 11 for Toolbox development.

9. **PlusCal/TLA⁺ Divergence Warnings**: After translating PlusCal to TLA⁺, manual edits to the generated TLA⁺ code can cause divergence warnings that must be manually dismissed (markers from version 1.7.0 may need manual removal).

10. **Global Mutable State in TLC**: TLC extensively uses global mutable variables, making it difficult to use as a library and causing potential issues when running multiple model checks in the same JVM process.

### Performance Considerations

11. **Custom Data Structures**: TLC uses custom implementations of collections (e.g., `tlc2.util.Vect`) instead of standard Java collections, which can have subtle performance and behavior differences.

12. **Sequential Liveness Checking**: TLC's strongly connected component (SCC) detection for liveness checking uses Tarjan's sequential algorithm, which doesn't scale to multiple cores and can be a bottleneck.

13. **Fingerprint Collisions**: TLC uses fingerprinting for state comparison. While extremely rare, hash collisions can theoretically cause TLC to miss states (though this has never been observed in practice with the current 64-bit fingerprints).

### IDE & User Experience

14. **macOS Notarization Requirements**: On macOS Catalina (10.15) and later, the Toolbox requires notarization. Unsigned or improperly notarized builds may be blocked by Gatekeeper.

15. **UTF-8 Mathematical Characters**: All source files use UTF-8 encoding and may contain mathematical characters, which can cause display issues in editors not configured for UTF-8.

16. **Test File Line Limit**: The `read_file` tool truncates output at 2000 lines, which can complicate work with large test files or specifications.

For more details on specific issues, check the [GitHub issues tracker](https://github.com/tlaplus/tlaplus/issues).

## Developing & Contributing

The TLA⁺ Tools and Toolbox IDE are both written in Java.
The TLA⁺ Tools source code is in [tlatools/org.lamport.tlatools](./tlatools/org.lamport.tlatools).
The Toolbox IDE is based on [Eclipse Platform](https://github.com/eclipse-platform) and is in the [toolbox](./toolbox) directory.
For instructions on building & testing these as well as setting up a development environment, see [DEVELOPING.md](DEVELOPING.md).

We welcome your contributions to this open source project!
TLA⁺ is used in safety-critical systems, so we have a contribution process in place to ensure quality is maintained; read [CONTRIBUTING.md](CONTRIBUTING.md) before beginning work.

## Roadmap: Potential Improvements

This section outlines potential improvements to the TLA⁺ tools, organized by area and difficulty. These range from low-hanging fruit to major architectural changes. See also [general/docs/contributions.md](general/docs/contributions.md) for more detailed project descriptions.

### Performance Improvements

#### Low-Hanging Fruit (Easy)

- **Replace Custom Collections with Java Standard Library**: Remove handwritten implementations like `tla2sany.utilities.Vector` and `tlc2.util.Vect` in favor of `java.util.ArrayList` and similar standard collections. Reduces maintenance burden and binary size.
  - **Impact**: Moderate (smaller JAR, less maintenance)
  - **Risk**: Low to Medium (subtle behavior differences need testing)
  - **Skills**: Java

- **Optimize Fingerprint Computation**: Profile and optimize hot paths in TLC's fingerprint calculation, which is called billions of times during model checking.
  - **Impact**: High (can speed up all model checking)
  - **Risk**: Low (well-isolated code)
  - **Skills**: Java, profiling tools

- **Add Caching for Frequently-Computed Values**: Memoize expensive computations in semantic analysis and model checking that are repeatedly evaluated.
  - **Impact**: Moderate
  - **Risk**: Low
  - **Skills**: Java

#### Medium-Hanging Fruit (Moderate)

- **Concurrent Strongly Connected Components (SCC) Detection**: Replace Tarjan's sequential SCC algorithm with a concurrent variant to enable multi-core liveness checking.
  - **Impact**: Very High (dramatically speeds up liveness checking)
  - **Risk**: High (requires formal verification of correctness)
  - **Skills**: Java, TLA⁺, concurrent algorithms, formal methods
  - **Note**: In progress - see contributions.md

- **Improve State Queue Data Structures**: Optimize TLC's state queue implementations for better cache locality and reduced memory allocations.
  - **Impact**: High
  - **Risk**: Medium
  - **Skills**: Java, data structures, performance tuning

- **Parallel State Expansion**: Enable TLC to expand multiple states in parallel more efficiently by reducing lock contention.
  - **Impact**: High
  - **Risk**: Medium to High
  - **Skills**: Java, concurrent programming

#### Not-So-Low-Hanging Fruit (High Difficulty)

- **Symbolic Model Checking Integration**: Add support for symbolic model checking techniques (BDDs or SAT/SMT) alongside explicit-state exploration.
  - **Impact**: Revolutionary (enables checking much larger state spaces)
  - **Risk**: Very High
  - **Skills**: Java, TLA⁺, BDDs, SAT/SMT solvers, formal methods

- **Incremental Model Checking**: Cache state exploration results and reuse them when specifications change slightly, avoiding full re-checks.
  - **Impact**: Very High (speeds up iterative development)
  - **Risk**: High
  - **Skills**: Java, TLA⁺, caching strategies

- **GPU-Accelerated Fingerprinting**: Offload fingerprint computation to GPUs for massive parallelization.
  - **Impact**: High (potentially)
  - **Risk**: Very High (major architectural change)
  - **Skills**: Java, CUDA/OpenCL, GPU programming

### Security Improvements

#### Low-Hanging Fruit (Easy)

- **Add Dependency Scanning**: Integrate tools like OWASP Dependency-Check to detect vulnerable dependencies.
  - **Impact**: High (prevents security issues)
  - **Risk**: Very Low
  - **Skills**: DevOps, CI/CD

- **Enable Security-Focused Linting**: Add SpotBugs or similar tools to catch common security anti-patterns.
  - **Impact**: Moderate
  - **Risk**: Very Low
  - **Skills**: Java, static analysis

- **Validate User Input**: Add proper validation and sanitization for file paths, command-line arguments, and configuration values to prevent injection attacks.
  - **Impact**: High
  - **Risk**: Low
  - **Skills**: Java, security best practices

#### Medium-Hanging Fruit (Moderate)

- **Sandbox TLC Execution**: Isolate TLC model checking in a sandboxed environment with restricted file system and network access.
  - **Impact**: High (prevents malicious specs from harming system)
  - **Risk**: Medium (may break legitimate use cases)
  - **Skills**: Java, security, sandboxing

- **Sign and Verify Modules**: Implement cryptographic signing for TLA⁺ modules to verify authenticity and integrity.
  - **Impact**: Moderate to High
  - **Risk**: Medium
  - **Skills**: Java, cryptography, PKI

#### Not-So-Low-Hanging Fruit (High Difficulty)

- **Formal Security Analysis of TLC**: Use formal methods to verify security properties of TLC itself, ensuring it can't be exploited via crafted specifications.
  - **Impact**: Very High (ultimate security confidence)
  - **Risk**: Low (research project)
  - **Skills**: TLA⁺, formal methods, security analysis

### Architectural Improvements

#### Low-Hanging Fruit (Easy)

- **Improve Internal Documentation**: Expand developer documentation, add architectural decision records (ADRs), and document key algorithms.
  - **Impact**: High (easier onboarding)
  - **Risk**: Very Low
  - **Skills**: Technical writing

- **Increase Test Coverage**: Add unit tests for undertested modules, particularly in SANY and PlusCal translator.
  - **Impact**: High (catches regressions)
  - **Risk**: Very Low
  - **Skills**: Java, JUnit

- **Extract Common Utilities**: Identify and extract reusable utility code into dedicated modules to reduce duplication.
  - **Impact**: Moderate
  - **Risk**: Low
  - **Skills**: Java, refactoring

#### Medium-Hanging Fruit (Moderate)

- **Improve TLC Error Reporting**: Replace cryptic error messages (including "null" errors) with helpful, actionable messages that guide users.
  - **Impact**: Very High (better user experience)
  - **Risk**: Low to Medium
  - **Skills**: Java, user experience

- **Create Runtime API for TLC**: Replace command-line interface with a bidirectional network API (REST, gRPC, JMX) to enable remote control, inspection, and metrics collection.
  - **Impact**: High (enables monitoring, cloud integration)
  - **Risk**: Medium
  - **Skills**: Java, API design, networking

- **Port Toolbox to Eclipse e4**: Migrate from Eclipse RCP 3.x to e4 for improved flexibility and reduced boilerplate.
  - **Impact**: Moderate (easier maintenance)
  - **Risk**: High (large migration effort)
  - **Skills**: Java, Eclipse RCP, e4

- **Modularize TLC Codebase**: Break TLC into well-defined modules with clear interfaces to improve maintainability and testability.
  - **Impact**: High
  - **Risk**: Medium to High
  - **Skills**: Java, software architecture

#### Not-So-Low-Hanging Fruit (High Difficulty)

- **Remove Global Mutable State from TLC**: Refactor TLC to eliminate global variables, enabling it to be used as a library and supporting multiple concurrent model checks in one JVM.
  - **Impact**: Very High (enables new use cases)
  - **Risk**: Very High (subtle soundness bugs possible)
  - **Skills**: Java, software architecture, extensive testing
  - **Note**: Must be done incrementally with extreme care

- **Language Server Protocol (LSP) Support**: Implement an LSP server for TLA⁺ to enable IDE support in VS Code, Vim, Emacs, and other editors.
  - **Impact**: Very High (massively expands accessibility)
  - **Risk**: High
  - **Skills**: Java/TypeScript, LSP, compilers

- **Plugin Architecture for TLC**: Enable users to write plugins that extend TLC's functionality (custom state space reductions, alternative storage backends, etc.).
  - **Impact**: High
  - **Risk**: High
  - **Skills**: Java, plugin architectures

### Tooling & User Experience

#### Low-Hanging Fruit (Easy)

- **Add Cloud Support for Google Compute**: Extend Cloud TLC to support Google Cloud Platform alongside AWS and Azure.
  - **Impact**: Moderate
  - **Skills**: jclouds, cloud platforms

- **Finish Unicode Support**: Complete remaining Unicode issues in the Toolbox editor.
  - **Impact**: Moderate
  - **Skills**: Eclipse, SANY

- **HTML Pretty-Printer**: Create `tla2html` tool similar to `tla2tex` but outputting interactive HTML with hyperlinks and collapsible proofs.
  - **Impact**: High (better documentation)
  - **Risk**: Low
  - **Skills**: Java, HTML, CSS

#### Medium-Hanging Fruit (Moderate)

- **Improved TLAPS Integration**: Better warning about unexpanded definitions, automatic expansion hints, and counter-example generation for invalid proof obligations.
  - **Impact**: High (easier formal proofs)
  - **Risk**: Medium
  - **Skills**: OCaml, TLA⁺, TLAPS

- **Interactive Debugger for TLC**: Step through state space exploration interactively, set breakpoints on states, and inspect variables.
  - **Impact**: Very High (revolutionary debugging experience)
  - **Risk**: Medium
  - **Skills**: Java, debugger protocols

- **Visualization Dashboard**: Real-time visualization of state space, state queue depth, coverage metrics, and worker utilization.
  - **Impact**: High
  - **Risk**: Low to Medium
  - **Skills**: Java, web technologies

#### Not-So-Low-Hanging Fruit (High Difficulty)

- **AI-Assisted Specification Writing**: Integrate LLMs to suggest invariants, help complete specifications, and explain model checking results.
  - **Impact**: Revolutionary (lowers barrier to entry)
  - **Risk**: High (requires careful design)
  - **Skills**: ML/AI, TLA⁺, UX design

### TLAPS (Proof System) Enhancements

These improvements require changes to TLAPS (separate repository), but are listed for completeness:

- **Automatic Operator Expansion** (Moderate): Automatically detect which definitions to expand using iterative deepening and heuristics
- **SMT Support for Regular Expressions** (Moderate to High): Integrate Z3/CVC4 regex support for reasoning about sequences
- **Counter-Example Generation** (Moderate to High): Connect Nunchaku or similar to generate counter-examples for invalid proofs
- **Liveness Checking with Symmetry** (High): Enable symmetry reduction for liveness properties

### Build & Infrastructure

#### Low-Hanging Fruit (Easy)

- **Migrate to GitHub Actions**: Fully migrate CI/CD from Jenkins to GitHub Actions for better integration and modern tooling
- **Add SonarQube Integration**: Automated code quality and technical debt tracking
- **Container-Based Builds**: Dockerize build environments for reproducible builds

#### Medium-Hanging Fruit (Moderate)

- **Automated Dependency Updates**: Use Dependabot or Renovate to keep dependencies current
- **Performance Regression Testing**: Automated benchmarks to detect performance regressions
- **Multi-Architecture Builds**: Support ARM64 (Apple Silicon, AWS Graviton) in addition to x86_64

### Priority Recommendations

**Start Here (Highest ROI):**
1. Improve TLC error reporting
2. Add comprehensive tests
3. Improve documentation
4. HTML pretty-printer
5. Dependency scanning

**High Impact, Reasonable Effort:**
1. Concurrent SCC detection
2. Runtime API for TLC
3. LSP server implementation
4. Interactive debugger

**Moonshots (High Risk, High Reward):**
1. Remove global mutable state
2. Symbolic model checking
3. AI-assisted specification
4. Incremental model checking

License & Copyright
-----------------
Copyright © 199? HP Corporation  
Copyright © 2003 Microsoft Corporation  
Copyright © 2023 Linux Foundation

Licensed under the [MIT License](LICENSE).

