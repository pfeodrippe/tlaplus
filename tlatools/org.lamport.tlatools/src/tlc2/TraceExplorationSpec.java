package tlc2;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Date;
import java.util.List;
import java.util.Optional;

import tlc2.input.MCParser;
import tlc2.input.MCParserResults;
import tlc2.model.MCError;
import tlc2.output.EC;
import tlc2.output.ErrorTraceMessagePrinterRecorder;
import tlc2.output.MP;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.impl.ModelConfig;
import tlc2.tool.impl.SpecProcessor;
import util.TLAConstants;

/**
 * Logic for generating a trace exploration (TE) spec.
 */
public class TraceExplorationSpec {
	
	/**
	 * Timestamp to include in TE spec module name.
	 */
	private final Date timestamp;
	
	/**
	 * Resolves TE spec files & provides output streams to them.
	 */
	private IStreamProvider streamProvider;
	
	/**
	 * Records TLC output as it runs, capturing the error trace if one is found.
	 */
	private final ErrorTraceMessagePrinterRecorder recorder;
	
	/**
	 * Initializes a new instance of the {@link TraceExplorationSpec} class.
	 * @param outputDirectory Directory to which to output the TE spec.
	 * @param timestamp Timestamp to include in TE spec filename.
	 * @param recorder Recorder to record TLC as it runs; assumed to already be subscribed.
	 */
	public TraceExplorationSpec(
			Path outputDirectory,
			Date timestamp,
			ErrorTraceMessagePrinterRecorder recorder) {
		this.timestamp = timestamp;
		this.streamProvider = new FileStreamProvider(outputDirectory);
		this.recorder = recorder;
	}
	
	/**
	 * Generates the TE spec and writes it to TLA and CFG files.
	 * @param specInfo Information about the original spec.
	 * @return Either TE spec details or an error message.
	 */
	public Optional<TraceExplorationSpecGenerationReport> generate(ITool specInfo) {
		return this.recorder.getMCErrorTrace().map(errorTrace -> {
			ModelConfig cfg = specInfo.getModelConfig();
			SpecProcessor spec = specInfo.getSpecProcessor();
			String ogModuleName = specInfo.getRootName();
			List<String> variables = Arrays.asList(TLCState.Empty.getVarsAsStrings());
			MCParserResults parserResults = MCParser.generateResultsFromProcessorAndConfig(spec, cfg);
			List<String> constants = parserResults.getModelConfig().getRawConstants();
			return this.generate(ogModuleName, constants, variables, errorTrace);
		});
	}

	/**
	 * Generates the TE spec and writes it to TLA and CFG files.
	 * @param ogModuleName Name of the original spec.
	 * @param constants Constants from the original spec; to be put into cfg file.
	 * 	example value: { "CONSTANT X <- XVal", "CONSTANT Y <- YVAL" }
	 * @param variables Variables from the original spec.
	 * 	example value: { "x", "y" }
	 * @param errorTrace The error trace.
	 */
	public 	TraceExplorationSpecGenerationReport generate(
			String ogModuleName,
			List<String> constants,
			List<String> variables,
			MCError errorTrace) {
		String teSpecModuleName = deriveTESpecModuleName(ogModuleName, this.timestamp);
		try (
				OutputStream tlaStream = this.streamProvider.getTlaStream(teSpecModuleName);
				OutputStream cfgStream = this.streamProvider.getCfgStream(teSpecModuleName);
		) {
			TraceExplorer.writeSpecTEStreams(
					teSpecModuleName,
					ogModuleName,
					null,
					constants,
					variables,
					errorTrace,
					tlaStream,
					cfgStream);
			TraceExplorationSpecGenerationReport report = new TraceExplorationSpecGenerationReport(
					errorTrace,
					this.streamProvider.getTlaPath(teSpecModuleName),
					this.streamProvider.getCfgPath(teSpecModuleName));
			MP.printMessage(EC.TLC_TE_SPEC_GENERATION_COMPLETE, report.teSpecTlaPath.toString());
			return report;
		} catch (SecurityException | IOException e) {
			MP.printMessage(EC.TLC_TE_SPEC_GENERATION_ERROR, e.getMessage());
		}
		return null;
	}
	
	public static String teModuleId(Date timestamp) {
		final long secondsSinceEpoch = timestamp.getTime() / 1_000L;
		return Long.toString(secondsSinceEpoch);
	}
	
	/**
	 * Derives the TE spec module name.
	 * @param ogModuleName Original module name.
	 * @return The TE spec module name.
	 */
	public static String deriveTESpecModuleName(String ogModuleName, Date timestamp) {
		// millis to seconds
		return String.format(
			"%s_%s_%s",
			ogModuleName,
			TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME,
			teModuleId(timestamp));
	}
	
	/**
	 * Determines whether the given spec is a TE spec.
	 * @param tlaFilePath Path to the TLA file.
	 * @return Whether the given spec is a TE spec.
	 */
	public static boolean isTESpecFile(String tlaFilePath) {
		if (null == tlaFilePath) {
			return false;
		}
		
		try {
			// TODO: branch based on something better than the filename such as the module
			// name that we choose above.
			String filename = Paths.get(tlaFilePath).getFileName().toString();
			// see tlc2.TraceExplorationSpec.deriveTESpecModuleName(String)
			return filename
					.matches("^.*_" + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + "_\\d{10}(.tla)?$");
		} catch (InvalidPathException e) { return false; }
	}
	
	/**
	 * Interface for creating streams to which to write the TE spec.
	 */
	public interface IStreamProvider {
		
		/**
		 * Returns the path to the TLA file.
		 * Path not guaranteed to exist.
		 * @param moduleName Name of the TE spec module.
		 * @return The path to the TLA file.
		 */
		public Path getTlaPath(String moduleName);
		
		/**
		 * Creates an output stream to which to write the TE spec.
		 * Caller is responsible for managing stream lifecycle.
		 * @param moduleName Name of the TE spec module.
		 * @return A new output stream to which to write the TE spec.
		 * @throws FileNotFoundException Thrown if filepath is inaccessible.
		 * @throws SecurityException Thrown if lacking perms to write file.
		 */
		public OutputStream getTlaStream(String moduleName) throws FileNotFoundException, SecurityException;
		
		/**
		 * Returns the path to the CFG file.
		 * Path not guaranteed to exist.
		 * @param moduleName Name of the TE spec module.
		 * @return The path to the CFG file.
		 */
		public Path getCfgPath(String moduleName);
		
		/**
		 * Creates an output stream to which to write the TE spec's CFG file.
		 * Caller is responsible for managing stream lifecycle.
		 * @param moduleName Name of the TE spec module.
		 * @return A new output stream to which to write the CFG file.
		 * @throws FileNotFoundException Thrown if filepath is inaccessible.
		 * @throws SecurityException Thrown if lacking perms to write file.
		 */
		public OutputStream getCfgStream(String moduleName) throws FileNotFoundException, SecurityException;
	}
	
	/**
	 * Provides streams to actual files on disk.
	 */
	public class FileStreamProvider implements IStreamProvider {
		
		/**
		 * Directory to which to output the files.
		 */
		private Path outputDirectory;
		
		/**
		 * Initializes a new instance of {@link FileStreamProvider}
		 * @param outputDirectory Output directory for TLA & CFG files.
		 */
		public FileStreamProvider(Path outputDirectory) {
			this.outputDirectory = outputDirectory;
		}
		
		@Override
		public Path getTlaPath(String moduleName) {
			return this.outputDirectory.resolve(moduleName + TLAConstants.Files.TLA_EXTENSION);
		}
		
		@Override
		public OutputStream getTlaStream(String moduleName) throws FileNotFoundException, SecurityException {
			this.ensureDirectoryExists();
			final File tlaFile = this.getTlaPath(moduleName).toFile();
			return new FileOutputStream(tlaFile);
		}
		
		@Override
		public Path getCfgPath(String moduleName) {
			return this.outputDirectory.resolve(moduleName + TLAConstants.Files.CONFIG_EXTENSION);
		}
		
		@Override
		public OutputStream getCfgStream(String moduleName) throws FileNotFoundException, SecurityException {
			this.ensureDirectoryExists();
			final File cfgFile = this.getCfgPath(moduleName).toFile();
			return new FileOutputStream(cfgFile);
		}
		
		/**
		 * Recursively creates directories until the desired path is present.
		 * @throws SecurityException Access issue when creating directories.
		 */
		private void ensureDirectoryExists() throws SecurityException {
			for (int i = 1; i <= this.outputDirectory.getNameCount(); i++) {
				Path subPath = this.outputDirectory.subpath(0, i);
				if (!subPath.toFile().exists()) {
					subPath.toFile().mkdir();
				}
			}
		}
	}
}
