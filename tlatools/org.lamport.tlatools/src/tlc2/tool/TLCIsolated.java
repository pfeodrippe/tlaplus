package tlc2.tool;

/**
 * Convenience facade exposing the isolated TLC execution helpers via simple
 * varargs-based methods. Intended for embedding scenarios where each TLC run
 * should execute in a fresh class loader without leaking global state back to
 * the host JVM.
 */
public final class TLCIsolated {

    private TLCIsolated() {
        // Utility.
    }

    /**
     * Executes TLC under an isolated class loader and returns its exit code.
     *
     * @param args command-line flags identical to those passed to the TLC main
     *             method
     * @return the numeric TLC exit code
     * @throws ReflectiveOperationException if TLC bootstrap fails
     */
    public static int run(final String... args) throws ReflectiveOperationException {
        return TLCIsolatedExecutor.run(args);
    }

    /**
     * Executes TLC under an isolated class loader and captures additional run
     * metadata, including the final error-trace value of {@code variableName}
     * when available.
     *
     * @param variableName the name of the state variable to read from the final
     *                     error trace; pass {@code null} to skip extraction
     * @param args         command-line flags identical to those passed to TLC
     * @return structured information about the run
     * @throws ReflectiveOperationException if TLC bootstrap fails
     */
    public static TLCIsolatedExecutor.RunOutcome runWithTrace(final String variableName,
            final String... args) throws ReflectiveOperationException {
        return TLCIsolatedExecutor.runWithErrorTrace(args, variableName);
    }

}
