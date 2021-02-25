package tlc2;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.locks.ReentrantLock;

import tlc2.input.MCOutputParser;
import tlc2.input.MCOutputPipeConsumer;
import tlc2.input.MCParser;
import tlc2.input.MCParserResults;
import tlc2.model.MCError;
import tlc2.model.MCState;
import tlc2.output.CFGCopier;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.Messages;
import tlc2.output.SpecTraceExpressionWriter;
import tlc2.tool.Defns;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.util.Vect;
import tlc2.value.impl.ModelValue;
import util.TLAConstants;
import util.ToolIO;
import util.UsageGenerator;

/**
 * This is an application class which provides the following functionalities:
 * 
 * 		. given a directory of a previously run model check (containing a .tla/.cfg/.out triplet), produce a "SpecTE"
 * 				.tla / .cfg file pair
 * 		. given a directory of a previously run model check (containing a .out file), dump a pretty print of the
 *				errors states to {@link System#out}
 * 		. given a directory of a previously run model check (containing a .tla/.cfg/.out triplet) and a file of
 * 				trace expressions, one per line, produce a "SpecTE" file pair, then run a model check
 * 				evaluating the expressions, writing the triplet TE.tla, TE.cfg, TE.out
 * 		. given a directory of a previously generated SpecTE file pair and a file of trace expressions, one per line,
 * 				run a model check evaluating the expressions, writing the triplet TE.tla, TE.cfg, TE.out
 *		. given an already executed output pipe consumer, generated a "SpecTE" .tla / .cfg pair
 */
public class TraceExplorer {
	private static final String GENERATE_SPEC_FUNCTION_PARAMETER_NAME = "-generateSpecTE";
	private static final String PRETTY_PRINT_FUNCTION_PARAMETER_NAME = "-prettyPrint";
	private static final String QUASI_REPL_PARAMETER_NAME = "-replBis";
	private static final String TRACE_EXPRESSIONS_FUNCTION_PARAMETER_NAME = "-traceExpressions";

    private static final String EXPRESSIONS_FILE_PARAMETER_NAME = "-expressionsFile";
    private static final String MODEL_CHECK_JVM_ARGUMENTS_PARAMETER_NAME = "-jvmArguments";
    private static final String MODEL_CHECK_TLC_ARGUMENTS_PARAMETER_NAME = "-tlcArguments";

    private static final String SOURCE_DIR_PARAMETER_NAME = "-source";
    private static final String GENERATE_SPEC_OVERWRITE_PARAMETER_NAME = "-overwrite";
    
    static final String SPEC_TE_INIT_ID = "_SpecTEInit";
    static final String SPEC_TE_NEXT_ID = "_SpecTENext";
    
    // <parameter name, whether the parameter takes an argument>
    private static final HashMap<String, Boolean> TLC_ARGUMENTS_TO_IGNORE;
    
    static {
    	TLC_ARGUMENTS_TO_IGNORE = new HashMap<>();
    	
    	TLC_ARGUMENTS_TO_IGNORE.put("-config", Boolean.TRUE);
    	TLC_ARGUMENTS_TO_IGNORE.put("-metadir", Boolean.TRUE);
    	TLC_ARGUMENTS_TO_IGNORE.put("-tool", Boolean.FALSE);
    }
    
    
    /**
	 * @return an array of length two; the 0-index is the location to the
	 *         destination TLA file, and the 1-index is that of the CFG file
	 */
	public static File[] writeSpecTEFiles(
			final File outputDirectory,
			final String osn,
			final String[] vars,
			final MCParserResults results,
			final MCError error)
					throws FileNotFoundException,
						SecurityException,
						IOException {

		final File specTETLA = new File(
				outputDirectory,
				TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME
				+ TLAConstants.Files.TLA_EXTENSION);
		final File specTECFG = new File(
				outputDirectory,
				TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME
				+ TLAConstants.Files.CONFIG_EXTENSION);
		
		List<String> variables = Arrays.asList(vars);

		try (
				FileOutputStream specTETLAOutStream = new FileOutputStream(specTETLA);
				FileOutputStream specTECFGOutStream = new FileOutputStream(specTECFG)
		) {
			writeSpecTEStreams(
					TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME,
					osn,
					results,
					variables,
					error,
					null,
					specTETLAOutStream,
					specTECFGOutStream);
		}

		return new File[] { specTETLA, specTECFG };
	}
	
	/**
	 * 
	 * @param teSpecModuleName
	 * @param originalSpecName
	 * @param originalSpecVariables
	 * @param results
	 * @param variables	 
	 * @param error
	 * @param specInfo
	 * @param specTETLAOutStream
	 * @param specTECFGOutStream
	 * @throws IOException
	 */
	public static void writeSpecTEStreams(
			final String teSpecModuleName,
			final String originalSpecName,
			final MCParserResults results,
			final List<String> variables,
			final MCError error,
			final ITool specInfo,
			final OutputStream specTETLAOutStream,
			final OutputStream specTECFGOutStream) throws IOException {

		final SpecTraceExpressionWriter writer = new SpecTraceExpressionWriter();

		// Each element in `constants` is a `Vect` with 2 elements.
		// The first element of this `Vect` is the key (the constant) and 
		// the second one is the value of the constant.
		Vect<Vect<Object>> constants = (Vect<Vect<Object>>) results.getModelConfig().getConstants();			

		// Get all reified constants;
		List<String> reifiedConstants = new ArrayList<String>();		
		for (Vect<Object> keyValuePair : (ArrayList<Vect<Object>>) Collections.list(constants.elements())) {
			reifiedConstants.add(keyValuePair.elementAt(0).toString());			
		}

		// Add all the model values as constants, they have to be reified (to mean something) in a TLA module.
		// First we set all the model values seen, the values will be at the static field ModelValue.mvs.
		ModelValue.setValues();
		List<String> mvsStr = new ArrayList<String>();
		for (ModelValue mv : ModelValue.mvs) {
			// Do not add the constant if it's already reified so we don't have 
			// duplicated constants error.
			if (!reifiedConstants.contains(mv.toString())) {
				mvsStr.add(mv.toString());
			}
		}		

		/**
		 * Write content of config file (SpecTE).
		 * <p>
		 * Contrary to the Toolbox's TraceExplorerDelegate, which reads constants,
		 * overrides, ... from the TLC model, this implementation copies all CONSTANT
		 * and CONSTANTS verbatim from the existing config file with which TLC ran. The
		 * definition that appear in the .tla file (e.g. MC.tla) don't have to be copied
		 * because SpecTE extends MC.
		 * We also add the model values as constants so they can be used for the traces at
		 * the TLA modules.
		 * (see TraceExplorerDelegate#writeModelInfo)
		 */
		List<String> mvsConfigConstants = new ArrayList<String>();
		for (String mv : mvsStr) {
			mvsConfigConstants.add(SpecTraceExpressionWriter.indentString(String.format("%s = %s", mv, mv), 1));
		}			

		if(!constants.isEmpty()) {
			List<String> indentedConstants = new ArrayList<String>();
			// Add `CONSTANTS` header.
			indentedConstants.add(TLAConstants.KeyWords.CONSTANTS);			
			for (Vect<Object> keyValuePair : (ArrayList<Vect<Object>>) Collections.list(constants.elements())) {
				String key = keyValuePair.elementAt(0).toString();
				String value = keyValuePair.elementAt(1).toString();
				indentedConstants.add(SpecTraceExpressionWriter.indentString(String.format("%s = %s", key, value), 1));
			}

			indentedConstants.addAll(mvsConfigConstants);
			writer.addConstants(indentedConstants);
		}

		// If needed, create module which contain the reified constants.
		// First we need to handle the case where a model value is defined in
		// the config file, but, for some reason, it's not used in any of the
		// model specs. E.g. I define `p1 = p1` in the `CONSTANTS` header of the
		// config file, but I do not use it (through `CONSTANTS`) in the model spec.
		// So we add these remaining constants to `mvsStr` so they are added to the 
		// `TE` spec.
		Defns defns = specInfo.getSpecProcessor().getDefns();
		ArrayList<String> modConstants = new ArrayList<String>();
		for (ModelValue mv : ModelValue.mvs) {
			if (defns.get(mv.toString()) == null) {
				modConstants.add(mv.toString());
			}
		}
		final String teConstantSpecName = String.format("%s_%s", originalSpecName, TLAConstants.TraceExplore.SPEC_TECONSTANTS_NAME);
		final Set<String> teConstantModuleHashSet = new HashSet<>();
		teConstantModuleHashSet.add(TLAConstants.BuiltInModules.TLC);
		String modelValuesAsConstants;
		if (!modConstants.isEmpty()) {
			teConstantModuleHashSet.add(teConstantSpecName);
			modelValuesAsConstants = String.format("CONSTANTS %s\n", String.join(", ", modConstants));
		}
		else {
			modelValuesAsConstants = "";
		}

		/**
		 * Write SpecTE.
		 */
		final Set<String> specTEExtendedModules = new HashSet<>();
		// A TE spec has to extend Toolbox to have access to _TETrace and _TEPosition
		// operators.
		specTEExtendedModules.add(TLAConstants.BuiltInModules.TRACE_EXPRESSIONS);
		// Adds Json module so we can write a Json output.
		specTEExtendedModules.add("Json");
		specTEExtendedModules.add("TLCExt");
		specTEExtendedModules.addAll(teConstantModuleHashSet);
				
		writer.addPrimer(teSpecModuleName, originalSpecName, specTEExtendedModules);		

		writer.addTraceExpressionInstance(
				String.format("%s_%s", originalSpecName, TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME));

		final List<MCState> trace = error.getStates();

		final String teTraceName = String.format("%s_%s", originalSpecName, TLAConstants.TraceExplore.SPEC_TETRACE_NAME);
		
		writer.addTraceFunctionInstance(teTraceName);
		
		writer.addProperties(trace, originalSpecName);

		// Write Init and Next with vars instead of extracting the vars from trace to
		// always write a syntactically correct behavior spec even if trace = <<>>.
		writer.addInitNextTraceFunction(trace, teSpecModuleName, variables, SPEC_TE_INIT_ID, SPEC_TE_NEXT_ID, results);
				
		writer.addFooter();
		
		/**
		 * Write definition of trace expression into new module.
		 */
		writer.append(TLAConstants.CR);
		
		final SpecTraceExpressionWriter te = new SpecTraceExpressionWriter();
		final String teModuleName = String.format("%s_%s", originalSpecName, TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME);
		te.append(TLAConstants.CR);
		
		writer.append(String.format(" Note that you can extract this module `%s`", teModuleName)).append(TLAConstants.CR);
		writer.append("  to a dedicated file to reuse `expression` (the module in the ").append(TLAConstants.CR);
		writer.append(String.format("  dedicated `%s.tla` file takes precedence ", teModuleName)).append(TLAConstants.CR);
		writer.append(String.format("  over the module `BlockingQueue_TEExpression` below).", teModuleName));
			
		te.addPrimer(teModuleName, originalSpecName, specTEExtendedModules);
		te.addTraceExpressionStub(originalSpecName, TLAConstants.TraceExplore.SPEC_TE_TRACE_EXPRESSION, variables);		
		te.addFooter();
		writer.append(TLAConstants.CR + te.toString() + TLAConstants.CR + TLAConstants.CR);
		
		/**
		 * Write commented definition of trace def override into new module.
		 * A user simply has to provide the serialized trace and uncomment the module.
		 */
		writer.append(TLAConstants.CR);
		writer.append("Parsing and semantic processing can take forever if the trace below is long.")
				.append(TLAConstants.CR);
		writer.append(" In this case, it is advised to deserialize the trace from a binary file.")
				.append(TLAConstants.CR);
		writer.append(" To create the file, replace your spec's invariant F with:").append(TLAConstants.CR);
		writer.append("  Inv == IF F THEN TRUE ELSE ~IOSerialize(Trace, \"file.bin\", TRUE)").append(TLAConstants.CR);
		writer.append(" (IOUtils module is from https://modules.tlapl.us/)");
		
		final Set<String> extendedModulesWithIOUtils = new HashSet<>();
		extendedModulesWithIOUtils.add("IOUtils");
		extendedModulesWithIOUtils.addAll(teConstantModuleHashSet);
		
		final SpecTraceExpressionWriter w = new SpecTraceExpressionWriter();
		w.append(TLAConstants.CR);
		w.addPrimer(teTraceName, originalSpecName, extendedModulesWithIOUtils);
		w.append(TLAConstants.TraceExplore.SPEC_TETRACE_TRACE_DEF).append(TLAConstants.DEFINES).append("IODeserialize(\"file.bin\", TRUE)\n\n");
		w.addFooter();
		// Users can uncomment the module if they wish to read the serialized trace.
		writer.append(TLAConstants.CR + w.getComment() + TLAConstants.CR + TLAConstants.CR);
		
		/**
		 * Write definition of trace def into new module.
		 */
		final Set<String> teTraceExtendedModules = new HashSet<>();
		teTraceExtendedModules.addAll(teConstantModuleHashSet);
		writer.addPrimer(teTraceName, originalSpecName, teTraceExtendedModules);

		writer.addTraceFunction(trace, TLAConstants.TraceExplore.SPEC_TETRACE_TRACE_DEF, TLAConstants.TraceExplore.SPEC_TETRACE_TRACE);
		
		writer.addAliasToCfg(TLAConstants.TraceExplore.SPEC_TE_TTRACE_EXPRESSION);		

		/**
		 * Write TEConstants module, if needed.
		 */
		if (modelValuesAsConstants != "") {
			writer.addFooter();
			writer.append(TLAConstants.CR);
			writer.addPrimer(teConstantSpecName, originalSpecName);
			writer.append(modelValuesAsConstants).append(TLAConstants.CR);
		}
		
        /**
         * Write to streams.
         */
		writer.writeStreams(specTETLAOutStream, specTECFGOutStream);
    }	    
    
    private enum RunMode {
    	GENERATE_SPEC_TE, PRETTY_PRINT, GENERATE_FROM_TLC_RUN, QUASI_REPL, TRACE_EXPLORATION;
    }

    
    private File specGenerationSourceDirectory;
    private String specGenerationOriginalSpecName;
    private boolean expectedOutputFromStdIn;
    private boolean overwriteGeneratedFiles;
    
    private List<String> expressions;
    private List<String> tlcArguments;
    
    private String replSpecName;
    private File temporaryREPLSpec;
    
    private RunMode runMode;

    /**
     * @param commandLineArguments arguments, ostensibly from the command line, with which this instance will configure
     * 								itself.
     */
    public TraceExplorer(final String[] commandLineArguments) {
    	processArguments(commandLineArguments);
    	
    	if (runMode == null) {
			printUsageAndExit();
    	}
    }
    
    protected final void processArguments(final String[] args) {
    	runMode = determineRunModeFromArguments(args);
    	if (runMode == null) {
    		return;
    	}

    	switch (runMode) {
			case QUASI_REPL:
			case TRACE_EXPLORATION:
	    		tlcArguments = new ArrayList<>();
				break;
			default:
				break;
    	}
    	
		specGenerationSourceDirectory = new File(System.getProperty("user.dir"));
		specGenerationOriginalSpecName = args[args.length - 1];
		expectedOutputFromStdIn = (specGenerationOriginalSpecName.charAt(0) == '-');
		if (expectedOutputFromStdIn) {
			specGenerationOriginalSpecName = null;
		} else if (RunMode.QUASI_REPL.equals(runMode)) {
			printUsageAndExit();
		}
		overwriteGeneratedFiles = false;

		String expressionsSourceFilename = null;
		
		boolean consumedAdditionalParameters = true;
		final int upperIndex = expectedOutputFromStdIn ? args.length : (args.length - 1);
    	int index = 0;
		while (consumedAdditionalParameters) {
			if (index < upperIndex) {
				final String nextArg = args[index];
				
				if (getRunModeForArgument(nextArg) != null) {
					index++;
					continue;
				}
				
				if (SOURCE_DIR_PARAMETER_NAME.equals(nextArg)) {
					index++;
					final String runDirectory = args[index++];
            		final File f = new File(runDirectory);
            		
            		if (!f.exists()) {
            			printErrorMessage("specified source directory does not exist.");
            			return;
            		}
            		
            		if (!f.isDirectory()) {
            			printErrorMessage("specified source directory is not a directory.");
            			return;
            		}
            		specGenerationSourceDirectory = f;

					index++;
				} else if (GENERATE_SPEC_OVERWRITE_PARAMETER_NAME.equals(nextArg)) {
					overwriteGeneratedFiles = true;
					
					index++;
				} else if (EXPRESSIONS_FILE_PARAMETER_NAME.equals(nextArg)) {
					index++;

					expressionsSourceFilename = args[index++];
				} else if (MODEL_CHECK_JVM_ARGUMENTS_PARAMETER_NAME.equals(nextArg)) {
					index++;

					final String argumentList = args[index++];
					final String[] arguments = argumentList.split(" ");
					TLCRunner.JVM_ARGUMENTS.addAll(Arrays.asList(arguments));
				} else if (MODEL_CHECK_TLC_ARGUMENTS_PARAMETER_NAME.equals(nextArg)) {
					index++;
					final String argumentList = args[index++];
					final String[] arguments = argumentList.split(" ");
					int argIndex = 0;
					
					while (argIndex < arguments.length) {
						final String argument = arguments[argIndex];
						final Boolean ignoreAdditionalParameter = TLC_ARGUMENTS_TO_IGNORE.get(argument);
						
						if (ignoreAdditionalParameter == null) {
							tlcArguments.add(argument);
						} else {
							if (ignoreAdditionalParameter.booleanValue()) {
								argIndex++;
							}
						}
						
						argIndex++;
					}
				} else {
    				consumedAdditionalParameters = false;
				}
			} else {
				consumedAdditionalParameters = false;
			}
		}
		
		if (RunMode.TRACE_EXPLORATION.equals(runMode) || RunMode.QUASI_REPL.equals(runMode)) {
			if (expressionsSourceFilename == null) {
    			printErrorMessage("no expressions file specified.");
				runMode = null;
				return;
			}
			
			final File sourceDirFile = new File(specGenerationSourceDirectory, expressionsSourceFilename);
			final File absoluteFile = new File(expressionsSourceFilename);
			final File f;
			if (sourceDirFile.exists()) {
				f = sourceDirFile;
			} else if (absoluteFile.exists()) {
				f = absoluteFile;
			} else {
				final String errorMessageSuffix;
				if (sourceDirFile.getAbsolutePath().equals(absoluteFile.getAbsolutePath())) {
					errorMessageSuffix = sourceDirFile.getAbsolutePath();
				} else {
					errorMessageSuffix = sourceDirFile.getAbsolutePath()
													+ " nor " + absoluteFile.getAbsolutePath();
				}
				printErrorMessage("an expressions file could not be found at " + errorMessageSuffix);
				runMode = null;
				return;
			}

			try {
				expressions = new ArrayList<>();
				try (final BufferedReader br = new BufferedReader(new FileReader(f))) {
					String line;
					while ((line = br.readLine()) != null) {
						final String trimmed = line.trim();
						
						if (trimmed.length() > 0) {
							expressions.add(trimmed);
						}
					}
				}
			} catch (final IOException e) {
				printErrorMessage("encountered an exception reading from expressions file "
									+ f.getAbsolutePath() + " :: " + e.getMessage());
				runMode = null;
				return;
			}

			if (RunMode.TRACE_EXPLORATION.equals(runMode)) {
				tlcArguments.add("-config");
				tlcArguments.add(TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME 
									+ TLAConstants.Files.CONFIG_EXTENSION);
				
				tlcArguments.add("-tool");
			} else {
				replSpecName = "repl"; //"REPL_" + System.currentTimeMillis();
				temporaryREPLSpec = new File(specGenerationSourceDirectory,
											 replSpecName + TLAConstants.Files.TLA_EXTENSION);
				temporaryREPLSpec.deleteOnExit();
			}

			tlcArguments.add("-metadir");
			tlcArguments.add(specGenerationSourceDirectory.getAbsolutePath());
			
			if (RunMode.TRACE_EXPLORATION.equals(runMode)) {
				tlcArguments.add(TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME);
			} else {
				tlcArguments.add(replSpecName);
			}
		}
     }
    
    /**
     * @return an {@link EC} defined error code representing success or failure.
     */
    public int execute() throws Exception {
    	if (RunMode.QUASI_REPL.equals(runMode)) {
    		return performREPL();
    	} else if (expectedOutputFromStdIn) {
    		return executeStreaming();
    	} else {
    		return executeNonStreaming();
    	}
    }
    
    private RunMode determineRunModeFromArguments(final String[] args) {
    	for (int i = 0; i < args.length; i++) {
    		final RunMode rm = getRunModeForArgument(args[i]);
    		
    		if (rm != null) {
    			return rm;
    		}
    	}

    	return null;
    }
    
    private RunMode getRunModeForArgument(final String arg) {
    	if (GENERATE_SPEC_FUNCTION_PARAMETER_NAME.equals(arg)) {
        	return RunMode.GENERATE_SPEC_TE;
        } else if (PRETTY_PRINT_FUNCTION_PARAMETER_NAME.equals(arg)) {
        	return RunMode.PRETTY_PRINT;
        } else if (TRACE_EXPRESSIONS_FUNCTION_PARAMETER_NAME.equals(arg)) {
        	return RunMode.TRACE_EXPLORATION;
        } else if (QUASI_REPL_PARAMETER_NAME.equals(arg)) {
        	return RunMode.QUASI_REPL;
        }
    	
    	return null;
    }
    
    private int executeNonStreaming() throws Exception {
    	if (!performPreFlightFileChecks()) {
			throw new IllegalStateException("There was an issue with the input, "
												+ TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + ", or "
												+ TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + " file.");
    	}
    	
		final boolean specifiedModuleIsSpecTE
					= specGenerationOriginalSpecName.equals(TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME);
		final boolean needGenerateSpecTE = RunMode.GENERATE_SPEC_TE.equals(runMode) 
											|| (!specifiedModuleIsSpecTE && RunMode.TRACE_EXPLORATION.equals(runMode));
    	if (needGenerateSpecTE) {
			final MCParser parser = new MCParser(specGenerationSourceDirectory, specGenerationOriginalSpecName);
    		final MCParserResults results = parser.parse();
    		
    		if (results.getOutputMessages().size() == 0) {
				MP.printMessage(EC.GENERAL, "The output file had no tool messages; was TLC not run with"
												+ " the '-tool' option when producing it?");

    			return EC.ExitStatus.ERROR;
    		} else if (results.getError() == null) {
    			final String msg;
    			if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
    				msg = "The output file contained no error-state messages, no "
    							+ TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + " will be produced.";
    			} else {
    				msg = "The output file contained no error-state messages, no "
								+ TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + " nor "
								+ TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + " will be produced, and, so, "
								+ "no trace expressions will be evaluated.";
    			}
				MP.printMessage(EC.GENERAL, msg);

    			return EC.NO_ERROR;
    		} else {
				try {
					writeSpecTEFiles(results, results.getError());

					if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
						return EC.NO_ERROR;
					} else if (RunMode.TRACE_EXPLORATION.equals(runMode)) { 	// currently always true
			    		return performTraceExploration();
			    	}
				} catch (final Exception e) { }
    		}
    	} else if (RunMode.PRETTY_PRINT.equals(runMode)) {
    		try {
	    		MCOutputParser.prettyPrintToStream(System.out, specGenerationSourceDirectory,
	    										   specGenerationOriginalSpecName);
				
				return EC.NO_ERROR;
    		} catch (final Exception e) { }
    	}
    	    	
		return EC.ExitStatus.ERROR;
    }
    
    private int executeStreaming() throws Exception {
    	final AtomicBoolean mcParserCompleted = new AtomicBoolean(false);
    	final ReentrantLock parseLock = new ReentrantLock();
    	final ArrayList<MCParser> parserList = new ArrayList<>(1);
		final MCOutputPipeConsumer.ConsumerLifespanListener listener
							= new MCOutputPipeConsumer.ConsumerLifespanListener() {
			@Override
			public void consumptionFoundSourceDirectoryAndSpecName(MCOutputPipeConsumer consumer) {
				specGenerationSourceDirectory = consumer.getSourceDirectory();
				specGenerationOriginalSpecName = consumer.getSpecName();
				
				final boolean specifiedModuleIsSpecTE
							= specGenerationOriginalSpecName.equals(TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME);
				final boolean needGenerateSpecTE
							= RunMode.GENERATE_SPEC_TE.equals(runMode)
											|| (!specifiedModuleIsSpecTE && RunMode.TRACE_EXPLORATION.equals(runMode));

				if (!performPreFlightFileChecks()) {
					throw new IllegalStateException("There was an issue with the input, "
														+ TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + ", or "
														+ TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + " file.");
				}

				if (needGenerateSpecTE) {
					MP.printMessage(EC.GENERAL,
							"Have encountered the source spec in the output logging, will begin parsing of those assets now.");
					
					final Runnable r = () -> {
						final MCParser parser
								= new MCParser(specGenerationSourceDirectory, specGenerationOriginalSpecName, true);
						parserList.add(parser);
						
						parseLock.lock();
						try {
							parser.parse();
						} finally {
							mcParserCompleted.set(true);
							parseLock.unlock();
						}
					};
					(new Thread(r)).start();
				}
			}
		};
		final MCOutputPipeConsumer pipeConsumer = new MCOutputPipeConsumer(System.in, listener);
		
		MP.printMessage(EC.GENERAL, "TraceExplorer is expecting input on stdin...");

		pipeConsumer.consumeOutput();
		
		if (pipeConsumer.outputHadNoToolMessages()) {
			MP.printMessage(EC.GENERAL, "The output had no tool messages; was TLC not run with"
					+ " the '-tool' option when producing it?");

			return EC.ExitStatus.ERROR;
		}

		MP.printMessage(EC.GENERAL, "Have received the final output logging message - finishing TraceExplorer work.");

		final boolean specifiedModuleIsSpecTE
				= specGenerationOriginalSpecName.equals(TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME);
		final boolean needGenerateSpecTE
				= RunMode.GENERATE_SPEC_TE.equals(runMode)
								|| (!specifiedModuleIsSpecTE && RunMode.TRACE_EXPLORATION.equals(runMode));
    	if (needGenerateSpecTE) {
    		if (pipeConsumer.getError() == null) {
    			final String msg;
    			if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
    				msg = "The output contained no error-state messages, no "
    							+ TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + " will be produced.";
    			} else {
    				msg = "The output contained no error-state messages, no "
								+ TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + " nor "
								+ TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + " will be produced, and, so, "
								+ "no trace expressions will be evaluated.";
    			}
				MP.printMessage(EC.GENERAL, msg);

    			return EC.NO_ERROR;
    		} else {
        		if (!mcParserCompleted.get()) {
        			parseLock.lock();
        		}
        		final MCParserResults results = parserList.get(0).getParseResults();
    			
				try {
					writeSpecTEFiles(results, pipeConsumer.getError());

					if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
						return EC.NO_ERROR;
					} else if (RunMode.TRACE_EXPLORATION.equals(runMode)) { 	// currently always true
			    		return performTraceExploration();
			    	}
				} catch (final Exception e) { }
    		}
    	} else if (RunMode.PRETTY_PRINT.equals(runMode)) {
    		if (pipeConsumer.getError() == null) {
    			MP.printMessage(EC.GENERAL, "The output contained no error-state messages; there is nothing to display.");
				
				return EC.NO_ERROR;
    		} else {
        		try {
    	    		MCOutputParser.prettyPrintToStream(System.out, pipeConsumer.getError());
    				
    				return EC.NO_ERROR;
        		} catch (final Exception e) { }
    		}
    	}
    	
		return EC.ExitStatus.ERROR;
    }
    
    private int performREPL() throws IOException {
    	final REPLSpecWriter writer = new REPLSpecWriter(replSpecName, expressions);
    	final File cfgFile = new File(specGenerationSourceDirectory, replSpecName + TLAConstants.Files.CONFIG_EXTENSION);
    	cfgFile.deleteOnExit();
    	writer.writeFiles(temporaryREPLSpec, cfgFile);

    	final REPLSpecWriter.REPLLogConsumerStream outputStream = new REPLSpecWriter.REPLLogConsumerStream();
		final TLCRunner tlcRunner = new TLCRunner(tlcArguments, outputStream);
		tlcRunner.setSilenceStdOut(true);
		final int errorCode = tlcRunner.run();
		
		System.out.println(String.join("\n", expressions));
		System.out.println("\t" + TLAConstants.EQ);
		// TODO indent on multi-line
		System.out.println("\t\t" + outputStream.getCollectedContent());

    	return errorCode;
    }
    
	private int performTraceExploration() throws IOException {
		final File tlaFile = new File(specGenerationSourceDirectory,
				TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION);
		final TraceExpressionExplorerSpecWriter writer = new TraceExpressionExplorerSpecWriter(expressions);
		final String configContent = writer.getConfigBuffer().toString();
		writer.writeFiles(tlaFile, null);

		final CFGCopier cfgCopier = new CFGCopier(TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME,
				TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME, specGenerationSourceDirectory, configContent);
		cfgCopier.copy();

		final File outFile = new File(specGenerationSourceDirectory,
				TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + TLAConstants.Files.OUTPUT_EXTENSION);
		final TLCRunner tlcRunner = new TLCRunner(tlcArguments, outFile);
		System.out.println("Forking TLC...");
		final int errorCode = tlcRunner.run();

		MCOutputParser.prettyPrintToStream(System.out, specGenerationSourceDirectory,
										   TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME);

		return errorCode;
	}

    private boolean performPreFlightFileChecks() {
		final boolean specifiedModuleIsSpecTE
				= specGenerationOriginalSpecName.equals(TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME);
		final boolean outputShouldExist = !expectedOutputFromStdIn 
											|| (specifiedModuleIsSpecTE && RunMode.TRACE_EXPLORATION.equals(runMode));

		String filename;
    	
    	if (outputShouldExist) {
    		filename = specGenerationOriginalSpecName + TLAConstants.Files.OUTPUT_EXTENSION;
    		final File outputFile = new File(specGenerationSourceDirectory, filename);
    		if (!outputFile.exists()) {
    			printErrorMessage("source directory (" + specGenerationSourceDirectory + ") does not contain "
    					+ filename);
    			
    			runMode = null;
    			return false;
    		}
    	}
    	
		if (RunMode.GENERATE_SPEC_TE.equals(runMode) || RunMode.TRACE_EXPLORATION.equals(runMode)) {
			filename = specGenerationOriginalSpecName + TLAConstants.Files.TLA_EXTENSION;
			final File tlaFile = new File(specGenerationSourceDirectory, filename);
			if (!tlaFile.exists()) {
				printErrorMessage("source directory (" + specGenerationSourceDirectory + ") does not contain "
						+ filename);
				
				runMode = null;
				return false;
			}
	    	
			filename = specGenerationOriginalSpecName + TLAConstants.Files.CONFIG_EXTENSION;
			final File configFile = new File(specGenerationSourceDirectory, filename);
			if (!configFile.exists()) {
				printErrorMessage("source directory (" + specGenerationSourceDirectory + ") does not contain "
						+ filename);
				
				runMode = null;
				return false;
			}
			
			if (!overwriteGeneratedFiles) {
				if (!specifiedModuleIsSpecTE) {
					final File specTETLA = new File(specGenerationSourceDirectory,
							(TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION));

					if (specTETLA.exists()) {
						printErrorMessage("specified source directory already contains " + specTETLA.getName()
								+ "; specify '" + GENERATE_SPEC_OVERWRITE_PARAMETER_NAME + "' to overwrite.");

						runMode = null;
						return false;
					}
				}
				
				if (RunMode.TRACE_EXPLORATION.equals(runMode)) {
					final File teTLA = new File(specGenerationSourceDirectory,
								(TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION));

					if (teTLA.exists()) {
						printErrorMessage("specified source directory already contains " + teTLA.getName()
								+ "; specify '" + GENERATE_SPEC_OVERWRITE_PARAMETER_NAME + "' to overwrite.");

						runMode = null;
						return false;
					}
				}
			}
		}
		
		return true;
    }
    
	private void writeSpecTEFiles(final MCParserResults results, final MCError error) throws IOException {
		writeSpecTEFiles(specGenerationSourceDirectory, specGenerationOriginalSpecName,
				// Not sure TLCState.Empty is correctly initialized at this point, but I don't
				// want to spend more time on it (screw you future Markus).
				TLCState.Empty.getVarsAsStrings(), results, error);
	}
    
    private void printErrorMessage(final String message) {
    	MP.printError(EC.GENERAL, message);
    }
    
    
    private static void printUsageAndExit() {
    	final List<List<UsageGenerator.Argument>> commandVariants = new ArrayList<>();
    	final UsageGenerator.Argument expressionFile
				= new UsageGenerator.Argument(EXPRESSIONS_FILE_PARAMETER_NAME, "file",
											 "expressions specified, one per line if being used in conjunction\n"
													+ "with " + TRACE_EXPRESSIONS_FUNCTION_PARAMETER_NAME
													+ " and just one if being used with "
													+ QUASI_REPL_PARAMETER_NAME
													+ "\nthis file must be in the source "
													+ "directory or specified by\nfull path", false);
    	final UsageGenerator.Argument jvmArguments
				= new UsageGenerator.Argument(MODEL_CHECK_JVM_ARGUMENTS_PARAMETER_NAME,
											  "\"-Xmx3072m -Xms512m\"",
											  "these arguments will be passed on to the TLC JVM when performing\n"
													+ "the model check",
											  true);
    	final UsageGenerator.Argument overwrite
	    		= new UsageGenerator.Argument(GENERATE_SPEC_OVERWRITE_PARAMETER_NAME,
	    									  "if specified, and if a SpecTE, or TE, file pair already exists,\n"
	    											+ "they will be overwritten; if they exist, and this has not been\n"
	    											+ "specified, the process will halt", true);
    	final UsageGenerator.Argument sourceDirectory
				= new UsageGenerator.Argument(SOURCE_DIR_PARAMETER_NAME, "path",
											  "the path to the directory containing tool output from model\n"
													+ "checking; defaults to CWD. This will be ignored if no SpecName\n"
													+ "has been specified (and so tool output will be expected to\n"
													+ "arrive on stdin)", true);
    	final UsageGenerator.Argument spec
				= new UsageGenerator.Argument("SpecName",
											  "if no spec name is specified, tool output will be expected to arrive\n"
													+ "via stdin and any " + SOURCE_DIR_PARAMETER_NAME
													+ " definition will be ignored.", false);
    	final UsageGenerator.Argument tlcArguments
				= new UsageGenerator.Argument(MODEL_CHECK_TLC_ARGUMENTS_PARAMETER_NAME,
											  "\"-some -other 2 -tlc arguments\"",
											  "these arguments will be passed on to TLC when performing the\n"
													+ "model check; -config, -tool, and -metadir will be ignored,\n"
													+ "if specified",
											  true);
    	
    	final List<UsageGenerator.Argument> traceExpressionsVariant = new ArrayList<>();
    	traceExpressionsVariant.add(jvmArguments);
    	traceExpressionsVariant.add(overwrite);
    	traceExpressionsVariant.add(sourceDirectory);
    	traceExpressionsVariant.add(tlcArguments);
    	traceExpressionsVariant.add(spec);
    	traceExpressionsVariant.add(expressionFile);
    	traceExpressionsVariant.add(new UsageGenerator.Argument(
    												TRACE_EXPRESSIONS_FUNCTION_PARAMETER_NAME,
    												"evaluate trace expressions in the context of an error state\n"
    													+ "specified through a generated SpecTE file; if the 'SpecName'\n"
    													+ "specified is anything other that 'SpecTE', the tool will\n"
    													+ "generate the SpecTE file pair, prior to generating the TE\n"
    													+ "file pair for the subsequently performed model checking",
    													false));
    	commandVariants.add(traceExpressionsVariant);

    	
    	final List<UsageGenerator.Argument> replBisVariant = new ArrayList<>();
    	replBisVariant.add(jvmArguments);
    	replBisVariant.add(tlcArguments);
    	replBisVariant.add(new UsageGenerator.Argument(
    												QUASI_REPL_PARAMETER_NAME,
    												"perform a one-off evaluation of an expression", false));
    	replBisVariant.add(expressionFile);
    	commandVariants.add(replBisVariant);

    	
    	final List<UsageGenerator.Argument> generateSpecVariant = new ArrayList<>();
    	generateSpecVariant.add(overwrite);
    	generateSpecVariant.add(sourceDirectory);
    	generateSpecVariant.add(spec);
    	generateSpecVariant.add(new UsageGenerator.Argument(
    												GENERATE_SPEC_FUNCTION_PARAMETER_NAME,
    												"generate a SpecTE tla/cfg pair from a model checking tool mode\n"
    													+ "output", false));
    	commandVariants.add(generateSpecVariant);

    	
    	final List<UsageGenerator.Argument> prettyPrintVariant = new ArrayList<>();
    	prettyPrintVariant.add(sourceDirectory);
    	prettyPrintVariant.add(spec);
    	prettyPrintVariant.add(new UsageGenerator.Argument(
    												PRETTY_PRINT_FUNCTION_PARAMETER_NAME,
    												"pretty print the error states of a model checking tool mode\n"
    													+ "output", false));
    	commandVariants.add(prettyPrintVariant);

    	
    	UsageGenerator.displayUsage(ToolIO.out, "TraceExplorer", TLCGlobals.versionOfTLC,
    								"a tool for working with TLC tool output and exploring trace expressions",
    								Messages.getString("TraceExplorerDescription"),
    								commandVariants, null, ' ');
    	
    	System.exit(-1);
    }
    
    /**
     * Ways to run this application:
     * 
     *  1. Evaluation of trace expressions from afrom an existing .tla/.out/.cfg triplet in which the .out contains
     *  	one or more MP.ERROR messages - see https://github.com/tlaplus/tlaplus/issues/393 for background:
     *  				java tlc2.TraceExplorer -traceExpressions \
     *  						-expressionsFile=_file_containing_expressions_one_per_line_ \
     *  						[-tlcArguments=_directory_containing_prior_run_output_] \
     *  						[-source=_directory_containing_prior_run_output_] \
     *  						[-overwrite] \
     *  						SpecName
     *  	the source directory defaults to CWD if not defined; the expressions file must either exist in the source
     *  	directory or be a full path; if TLC arguments are specified (all within quotes) they will be passed on to
     *  	TLC when performing the model check; -config, -tool, and -metadir will be ignored, if specified;  if no
     *  	SpecName is specified then we will expect the output data to arrive on stdin - anything specified via
     *  	-source will be ignore in this case as we will derive that from the output log content.
     *  
     *  2. Evaluation of an expression, ala REPL-ese:
     *  				java tlc2.TraceExplorer -replBis \
     *  						-expressionsFile=_file_containing_expressions_to_evaluate_ \
     *  						[-tlcArguments=_directory_containing_prior_run_output_]
     *  	the expressions file must either exist in the source directory or be a full path; if TLC arguments are
     *  	specified (all within quotes) they will be passed on to TLC when performing the model check; -config,
     *  	-tool, and -metadir will be ignored, if specified
     *  
     *  3. Generation of a 'SpecTE.tla' from an existing .tla/.out/.cfg triplet in which the .out contains
     *  	one or more MP.ERROR messages - see https://github.com/tlaplus/tlaplus/issues/393 for background:
     *  				java tlc2.TraceExplorer -generateSpecTE \
     *  						[-source=_directory_containing_prior_run_output_] \
     *  						[-overwrite] \
     *  						SpecName
     *  	the source directory defaults to CWD if not defined; if overwrite is not specified and a SpecTE.tla
     *  	already exists in the source directory, execution will halt; if no SpecName is specified then we
     *  	will expect the output data to arrive on stdin - anything specified via -source will be ignore in this
     *  	case as we will derive that from the output log content.
     *  
     *  4. Pretty print the error states from an existing .out file to {@link System#out}:
     *  				java tlc2.TraceExplorer -prettyPrint \
     *  						[-source=_directory_containing_prior_run_output_] \
     *  						SpecName
     *  	the source directory defaults to CWD if not defined; if no SpecName is specified then we
     *  	will expect the output data to arrive on stdin - anything specified via -source will be ignore in this
     *  	case as we will derive that from the output log content.
     */
    public static void main(final String[] args) {
    	if (args.length == 0) {
    		printUsageAndExit();
    	}
    	
    	try {
        	final TraceExplorer te = new TraceExplorer(args);
	    	final int returnCode = te.execute();
	    	
	    	System.exit(returnCode);
    	} catch (final Exception e) {
    		System.err.println("Caught exception: " + e.getLocalizedMessage());
    		
    		printUsageAndExit();
    	}
    }
}
