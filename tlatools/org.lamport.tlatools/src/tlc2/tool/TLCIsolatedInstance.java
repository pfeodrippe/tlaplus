package tlc2.tool;

import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;

import tlc2.util.ChildFirstClassLoader;
import tlc2.util.ClassPathCollector;

final class TLCIsolatedInstance implements AutoCloseable {

    private final ChildFirstClassLoader loader;
    private Object delegate;
    private Method handleParameters;
    private Method checkEnvironment;
    private Method process;
    private Method setResolver;
    private Method getMainFile;
    private Field modelPartOfJarField;
    private Method parseDirname;
    private Constructor<?> simpleFilenameToStreamDefaultCtor;
    private Constructor<?> simpleFilenameToStreamDirCtor;
    private Constructor<?> inJarFilenameToStreamCtor;
    private Field modelInJarPathField;
    private Field recorderField;
    private Method recorderGetMCErrorTrace;
    private Method mcErrorGetStates;
    private Method mcStateGetVariables;
    private Method mcVariableGetName;
    private Method mcVariableGetTLCValue;
    private Field intValueValField;
    private Field mainCheckerField;
    private Field metaDirField;
    private Method getNumWorkersMethod;

    private TLCIsolatedInstance(final ChildFirstClassLoader loader,
                                final Object delegate,
                                final Method handleParameters,
                                final Method checkEnvironment,
                                final Method process,
                                final Method setResolver,
                                final Method getMainFile,
                                final Field modelPartOfJarField,
                                final Method parseDirname,
                                final Constructor<?> simpleFilenameToStreamDefaultCtor,
                                final Constructor<?> simpleFilenameToStreamDirCtor,
                                final Constructor<?> inJarFilenameToStreamCtor,
                                final Field modelInJarPathField,
                                final Field recorderField,
                                final Method recorderGetMCErrorTrace,
                                final Method mcErrorGetStates,
                                final Method mcStateGetVariables,
                                final Method mcVariableGetName,
                                final Method mcVariableGetTLCValue,
                                final Field intValueValField,
                                final Field mainCheckerField,
                                final Field metaDirField,
                                final Method getNumWorkersMethod) {
        this.loader = loader;
        this.delegate = delegate;
        this.handleParameters = handleParameters;
        this.checkEnvironment = checkEnvironment;
        this.process = process;
        this.setResolver = setResolver;
        this.getMainFile = getMainFile;
        this.modelPartOfJarField = modelPartOfJarField;
        this.parseDirname = parseDirname;
        this.simpleFilenameToStreamDefaultCtor = simpleFilenameToStreamDefaultCtor;
        this.simpleFilenameToStreamDirCtor = simpleFilenameToStreamDirCtor;
        this.inJarFilenameToStreamCtor = inJarFilenameToStreamCtor;
        this.modelInJarPathField = modelInJarPathField;
        this.recorderField = recorderField;
        this.recorderGetMCErrorTrace = recorderGetMCErrorTrace;
        this.mcErrorGetStates = mcErrorGetStates;
        this.mcStateGetVariables = mcStateGetVariables;
        this.mcVariableGetName = mcVariableGetName;
        this.mcVariableGetTLCValue = mcVariableGetTLCValue;
    this.intValueValField = intValueValField;
        this.mainCheckerField = mainCheckerField;
        this.metaDirField = metaDirField;
        this.getNumWorkersMethod = getNumWorkersMethod;
    }

    static TLCIsolatedInstance create() throws ReflectiveOperationException {
        final ChildFirstClassLoader loader = new ChildFirstClassLoader(ClassPathCollector.collect(),
                TLCIsolatedInstance.class.getClassLoader());

        final Class<?> tlcClass = Class.forName("tlc2.TLC", true, loader);
        final Object delegate = tlcClass.getDeclaredConstructor().newInstance();

        final Method handleParameters = tlcClass.getMethod("handleParameters", String[].class);
        final Method checkEnvironment = tlcClass.getDeclaredMethod("checkEnvironment");
        checkEnvironment.setAccessible(true);
        final Method process = tlcClass.getMethod("process");

        final Class<?> filenameToStreamClass = Class.forName("util.FilenameToStream", false, loader);
        final Method setResolver = tlcClass.getMethod("setResolver", filenameToStreamClass);
        final Method getMainFile = tlcClass.getMethod("getMainFile");

        final Field modelPartOfJarField = tlcClass.getDeclaredField("modelPartOfJar");
        modelPartOfJarField.setAccessible(true);

        final Class<?> fileUtilClass = Class.forName("util.FileUtil", true, loader);
        final Method parseDirname = fileUtilClass.getMethod("parseDirname", String.class);

        final Class<?> simpleFilenameToStreamClass = Class.forName("util.SimpleFilenameToStream", true, loader);
        final Constructor<?> simpleFilenameToStreamDefaultCtor = simpleFilenameToStreamClass.getConstructor();
        final Constructor<?> simpleFilenameToStreamDirCtor = simpleFilenameToStreamClass.getConstructor(String.class);

        final Class<?> inJarFilenameToStreamClass = Class.forName("model.InJarFilenameToStream", true, loader);
        final Constructor<?> inJarFilenameToStreamCtor = inJarFilenameToStreamClass.getConstructor(String.class);
        final Class<?> modelInJarClass = Class.forName("model.ModelInJar", true, loader);
        final Field modelInJarPathField = modelInJarClass.getField("PATH");

        final Field recorderField = tlcClass.getDeclaredField("recorder");
        recorderField.setAccessible(true);
        final Class<?> recorderClass = Class.forName("tlc2.output.ErrorTraceMessagePrinterRecorder", true, loader);
        final Method recorderGetMCErrorTrace = recorderClass.getMethod("getMCErrorTrace");
        final Class<?> mcErrorClass = Class.forName("tlc2.model.MCError", true, loader);
        final Method mcErrorGetStates = mcErrorClass.getMethod("getStates");
        final Class<?> mcStateClass = Class.forName("tlc2.model.MCState", true, loader);
        final Method mcStateGetVariables = mcStateClass.getMethod("getVariables");
        final Class<?> mcVariableClass = Class.forName("tlc2.model.MCVariable", true, loader);
        final Method mcVariableGetName = mcVariableClass.getMethod("getName");
        final Method mcVariableGetTLCValue = mcVariableClass.getMethod("getTLCValue");
        final Class<?> intValueClass = Class.forName("tlc2.value.impl.IntValue", true, loader);
        final Field intValueValField = intValueClass.getField("val");

    final Class<?> globalsClass = Class.forName("tlc2.TLCGlobals", true, loader);
    final Field mainCheckerField = globalsClass.getDeclaredField("mainChecker");
        mainCheckerField.setAccessible(true);
        final Field metaDirField = globalsClass.getDeclaredField("metaDir");
        metaDirField.setAccessible(true);
        final Method getNumWorkersMethod = globalsClass.getMethod("getNumWorkers");

        return new TLCIsolatedInstance(loader, delegate, handleParameters, checkEnvironment, process, setResolver,
                getMainFile, modelPartOfJarField, parseDirname, simpleFilenameToStreamDefaultCtor,
                simpleFilenameToStreamDirCtor, inJarFilenameToStreamCtor, modelInJarPathField, recorderField,
                recorderGetMCErrorTrace, mcErrorGetStates, mcStateGetVariables, mcVariableGetName,
                mcVariableGetTLCValue, intValueValField, mainCheckerField, metaDirField, getNumWorkersMethod);
    }

    boolean handleParameters(final String[] args) throws ReflectiveOperationException {
        return (Boolean) handleParameters.invoke(delegate, new Object[] { args });
    }

    boolean checkEnvironment() throws ReflectiveOperationException {
        return (Boolean) checkEnvironment.invoke(delegate);
    }

    void configureResolver() throws ReflectiveOperationException {
        final boolean modelInJar = modelPartOfJarField.getBoolean(delegate);
        final Object resolver;
        if (modelInJar) {
            final String path = (String) modelInJarPathField.get(null);
            resolver = inJarFilenameToStreamCtor.newInstance(path);
        } else {
            final String mainFile = (String) getMainFile.invoke(delegate);
            final String dir = (String) parseDirname.invoke(null, mainFile);
            if (dir != null && !dir.isEmpty()) {
                resolver = simpleFilenameToStreamDirCtor.newInstance(dir);
            } else {
                resolver = simpleFilenameToStreamDefaultCtor.newInstance();
            }
        }
        setResolver.invoke(delegate, resolver);
    }

    int process() throws ReflectiveOperationException {
        return ((Integer) process.invoke(delegate)).intValue();
    }

    int getLastErrorTraceIntValue(final String variableName) throws ReflectiveOperationException {
        final Object recorder = recorderField.get(delegate);
        @SuppressWarnings("unchecked")
        final java.util.Optional<Object> optional = (java.util.Optional<Object>) recorderGetMCErrorTrace
                .invoke(recorder);
        if (!optional.isPresent()) {
            throw new IllegalStateException("No error trace available from TLC run");
        }
        final Object mcError = optional.get();
        @SuppressWarnings("unchecked")
        final java.util.List<Object> states = (java.util.List<Object>) mcErrorGetStates.invoke(mcError);
        if (states.isEmpty()) {
            throw new IllegalStateException("Error trace did not contain any states");
        }
        final Object lastState = states.get(states.size() - 1);
        final Object[] variables = (Object[]) mcStateGetVariables.invoke(lastState);
        for (final Object variable : variables) {
            final String name = (String) mcVariableGetName.invoke(variable);
            if (variableName.equals(name)) {
                final Object value = mcVariableGetTLCValue.invoke(variable);
                if (value == null) {
                    throw new IllegalStateException("Variable " + variableName + " lacks TLC value representation");
                }
                return intValueValField.getInt(value);
            }
        }
        throw new IllegalStateException("Variable " + variableName + " not found in error trace");
    }

    int getMainCheckerIdentity() throws ReflectiveOperationException {
        final Object checker = mainCheckerField.get(null);
        return checker == null ? 0 : System.identityHashCode(checker);
    }

    String getMetaDir() throws ReflectiveOperationException {
        return (String) metaDirField.get(null);
    }

    int getNumWorkers() throws ReflectiveOperationException {
        return ((Integer) getNumWorkersMethod.invoke(null)).intValue();
    }

    @Override
    public void close() {
        try {
            loader.close();
        } catch (final IOException e) {
            throw new RuntimeException(e);
        } finally {
            delegate = null;
            handleParameters = null;
            checkEnvironment = null;
            process = null;
            setResolver = null;
            getMainFile = null;
            modelPartOfJarField = null;
            parseDirname = null;
            simpleFilenameToStreamDefaultCtor = null;
            simpleFilenameToStreamDirCtor = null;
            inJarFilenameToStreamCtor = null;
            modelInJarPathField = null;
            recorderField = null;
            recorderGetMCErrorTrace = null;
            mcErrorGetStates = null;
            mcStateGetVariables = null;
            mcVariableGetName = null;
            mcVariableGetTLCValue = null;
            intValueValField = null;
            mainCheckerField = null;
            metaDirField = null;
            getNumWorkersMethod = null;
        }
    }
}
