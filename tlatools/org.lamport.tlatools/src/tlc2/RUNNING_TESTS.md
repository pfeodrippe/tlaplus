Commands used to build and run the ManualRunTwiceTest

Run these from the repository root or the `tlatools/org.lamport.tlatools` directory.

1) Build the distribution JAR (provides `tla2tools.jar` and dependency expansion used by tests):

```bash
cd tlatools/org.lamport.tlatools
ant -f customBuild.xml dist
```

2) Compile the manual test runner (uses the generated `dist/tla2tools.jar` on the classpath):

```bash
cd tlatools/org.lamport.tlatools
javac -cp "dist/tla2tools.jar" -d class test-verify/tlc2/tool/ManualRunTwiceTest.java
```

3) Run the manual test runner (prints lifecycle markers and includes an internal watchdog):

```bash
cd tlatools/org.lamport.tlatools
# Ensure edited classes in `class` override any classes bundled inside the jar
java -cp "class:dist/tla2tools.jar" tlc2.tool.ManualRunTwiceTest
```

Notes:
- The manual runner currently comments out the second TLC run to help isolate the hang.
- The runner uses a watchdog that forcefully halts the JVM if execution does not complete within 10 seconds.
- If you want to run tests through Ant/JUnit, use `ant -f customBuild.xml test-set -Dtest.testcases="<path-to-test>"` (see `DEVELOPING.md`).

Additional test: RunTwiceJUnitTest
----------------------------------

We added a focused unit test that verifies TLC runs in the same JVM must reset global state between runs.

- Test class: `test/tlc2/tool/RunTwiceJUnitTest.java`
- What it does: Runs two small TLA+ models (`test-model/ModelA.tla` and `test-model/ModelB.tla`) and asserts that a second run without calling `TLCGlobals.reset()` does not silently succeed. It then demonstrates the correct flow by resetting globals and re-running `ModelB`.
- How to run locally via Ant (recommended):

```bash
cd tlatools/org.lamport.tlatools
ant -f customBuild.xml test-set -Dtest.testcases="tlc2/tool/RunTwiceJUnitTest.java"
```

Notes:
- The test is already included explicitly in `customBuild.xml` so CI will run it as part of the normal test-set.
- The test intentionally uses small models with invariant violations so the test output and exit codes are easy to inspect.

