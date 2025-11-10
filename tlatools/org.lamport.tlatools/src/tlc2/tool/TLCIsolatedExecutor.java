package tlc2.tool;

/**
 * Runs TLC inside an isolated class loader so each invocation starts from a
 * pristine static state equivalent to the initial JVM load.
 */
public final class TLCIsolatedExecutor {

    private TLCIsolatedExecutor() {
        // Utility.
    }

    public static int run(final String[] args) throws ReflectiveOperationException {
        try (TLCIsolatedInstance instance = TLCIsolatedInstance.create()) {
            if (!instance.handleParameters(args)) {
                return 1;
            }
            if (!instance.checkEnvironment()) {
                return 1;
            }
            instance.configureResolver();
            return instance.process();
        }
    }
    public static RunOutcome runWithErrorTrace(final String[] args, final String variableName)
            throws ReflectiveOperationException {
        try (TLCIsolatedInstance instance = TLCIsolatedInstance.create()) {
            if (!instance.handleParameters(args)) {
                return new RunOutcome(1, null, 0, null, 0);
            }
            if (!instance.checkEnvironment()) {
                return new RunOutcome(1, null, 0, null, 0);
            }
            instance.configureResolver();
            final int exitCode = instance.process();
            Integer lastValue = null;
            if (variableName != null) {
                try {
                    lastValue = Integer.valueOf(instance.getLastErrorTraceIntValue(variableName));
                } catch (final IllegalStateException e) {
                    // Leave lastValue as null when no error trace is available.
                }
            }
            final int checkerId = instance.getMainCheckerIdentity();
            final String metaDir = instance.getMetaDir();
            final int numWorkers = instance.getNumWorkers();
            return new RunOutcome(exitCode, lastValue, checkerId, metaDir, numWorkers);
        }
    }

    public static final class RunOutcome {
        private final int exitCode;
        private final Integer lastIntValue;
        private final int mainCheckerIdentity;
        private final String metaDir;
        private final int numWorkers;

        private RunOutcome(final int exitCode, final Integer lastIntValue) {
            this(exitCode, lastIntValue, 0, null, 0);
        }

        private RunOutcome(final int exitCode, final Integer lastIntValue, final int mainCheckerIdentity,
                final String metaDir, final int numWorkers) {
            this.exitCode = exitCode;
            this.lastIntValue = lastIntValue;
            this.mainCheckerIdentity = mainCheckerIdentity;
            this.metaDir = metaDir;
            this.numWorkers = numWorkers;
        }

        public int getExitCode() {
            return exitCode;
        }

        public Integer getLastIntValue() {
            return lastIntValue;
        }

        public int getMainCheckerIdentity() {
            return mainCheckerIdentity;
        }

        public String getMetaDir() {
            return metaDir;
        }

        public int getNumWorkers() {
            return numWorkers;
        }
    }
}
