package tlc2.tool;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.Test;

public class RunTwiceIsolatedClassLoaderTest {

    private static final Path SPEC_FILE = Paths.get("test-model/IsolatedDynamicSpec.tla");
    private static final Path CFG_FILE = Paths.get("test-model/IsolatedDynamicSpec.cfg");

    @Test
    public void testIsolatedRunsStartFromPristineState() throws Exception {
        writeSpecVariantOne();
        final TLCIsolatedExecutor.RunOutcome runOne = runWithIsolatedExecutor("run1");
        if (runOne.getExitCode() != 2110) {
            throw new AssertionError("Expected exit code 2110 for variant one but got " + runOne.getExitCode());
        }
        if (runOne.getLastIntValue() == null || runOne.getLastIntValue().intValue() != 3) {
            throw new AssertionError("Expected final x state of 3 for variant one but got " + runOne.getLastIntValue());
        }

        writeSpecVariantTwo();
        final TLCIsolatedExecutor.RunOutcome runTwo = runWithIsolatedExecutor("run2");
        if (runTwo.getExitCode() == runOne.getExitCode()) {
            throw new AssertionError("Second run should not mirror first run exit code; got " + runTwo.getExitCode());
        }
        if (runTwo.getMainCheckerIdentity() == runOne.getMainCheckerIdentity()) {
            throw new AssertionError("Main checker identity should differ across isolated runs");
        }
        assertMetaDir(runOne.getMetaDir(), "states/RunTwiceIsolatedClassLoaderTest/run1");
        assertMetaDir(runTwo.getMetaDir(), "states/RunTwiceIsolatedClassLoaderTest/run2");
        if (runOne.getNumWorkers() != 1 || runTwo.getNumWorkers() != 1) {
            throw new AssertionError("Isolated runs should reflect configured worker count of 1");
        }
    }

    private static TLCIsolatedExecutor.RunOutcome runWithIsolatedExecutor(final String runId)
            throws ReflectiveOperationException {
        final String[] args = new String[] {
                "-workers", "1",
                "-metadir", "states/RunTwiceIsolatedClassLoaderTest/" + runId,
                "-noTE",
                "-noTEBin",
                SPEC_FILE.toString()
        };
        return TLCIsolatedExecutor.runWithErrorTrace(args, "x");
    }

    private static void assertMetaDir(final String actual, final String expected) {
        if (actual == null) {
            throw new AssertionError("Metadir should not be null");
        }
        final String normalized = actual.endsWith("/") ? actual.substring(0, actual.length() - 1) : actual;
        if (!expected.equals(normalized)) {
            throw new AssertionError("Expected metadir " + expected + " but saw " + actual);
        }
    }

    private static void writeSpecVariantOne() throws IOException {
        final String content = String.join("\n",
                "---- MODULE IsolatedDynamicSpec ----",
                "EXTENDS Integers",
                "VARIABLE x",
                "TheOp == 1 + 1",
                "Init == x = 0",
                "Action == /\\ x < 5 /\\ x' = x + 1",
                "Next == Action \\/ (x = 5 /\\ UNCHANGED x)",
                "Inv == x <= TheOp",
                "Spec == Init /\\ [][Next]_x",
                "====",
                "");
        writeFiles(content);
    }

    private static void writeSpecVariantTwo() throws IOException {
        final String content = String.join("\n",
                "---- MODULE IsolatedDynamicSpec ----",
                "EXTENDS Integers",
                "VARIABLE x",
                "TheOp == 4 + 4",
                "Init == x = 0",
                "Action == ( /\\ x < 8 /\\ x' = x + 1 ) \\/ ( /\\ x = 8 /\\ UNCHANGED x )",
                "Next == Action",
                "Inv == x <= TheOp",
                "Spec == Init /\\ [][Next]_x",
                "====",
                "");
        writeFiles(content);
    }

    private static void writeFiles(final String specContent) throws IOException {
        Files.createDirectories(SPEC_FILE.getParent());
        Files.writeString(SPEC_FILE, specContent);
        Files.writeString(CFG_FILE, String.join("\n",
                "INIT Init",
                "NEXT Next",
                "INVARIANT Inv",
                ""));
    }
}
