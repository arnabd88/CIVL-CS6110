package edu.udel.cis.vsl.civl.run.common;

import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.CIVLMacroO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.analyzeAbsO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.astO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.checkDivisionByZeroO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.checkMemoryLeakO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.collectHeapsO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.collectOutputO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.collectProcessesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.collectScopesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.deadlockO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.debugO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.echoO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.enablePrintfO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.errorBoundO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.guiO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.guidedO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.idO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.inputO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.macroO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.maxdepthO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.minO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.mpiContractO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.ompLoopDecompO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.ompNoSimplifyO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.preprocO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.procBoundO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.pthreadOnlyO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.randomO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.saveStatesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.seedO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showAmpleSetO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showAmpleSetWtStatesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showInputVarsO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showMemoryUnitsO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showModelO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showPathConditionO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showProgramO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showProverQueriesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showQueriesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showSavedStatesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showStatesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showTimeO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showTransitionsO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showUnreachedCodeO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.simplifyO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.solveO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.statelessPrintfO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.strictCompareO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.svcomp16O;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.sysIncludePathO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.timeoutO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.traceO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.userIncludePathO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.verboseO;

import java.io.PrintStream;
import java.util.Collection;
import java.util.SortedMap;
import java.util.TreeMap;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.run.IF.CommandLine;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandLineKind;
import edu.udel.cis.vsl.civl.run.common.NormalCommandLine.NormalCommandKind;
import edu.udel.cis.vsl.gmc.Option;

public class CIVLCommand {

	private static SortedMap<String, Option> showOptions = new TreeMap<>();
	private static SortedMap<String, Option> verifyOptions = new TreeMap<>();
	private static SortedMap<String, Option> compareOptions = new TreeMap<>();
	private static SortedMap<String, Option> replayOptions = new TreeMap<>();
	private static SortedMap<String, Option> runOptions = new TreeMap<>();

	static {
		CIVLCommand.addShowOption(showModelO, verboseO, debugO, echoO,
				userIncludePathO, sysIncludePathO, svcomp16O, pthreadOnlyO, showInputVarsO,
				showProgramO, ompNoSimplifyO, ompLoopDecompO, macroO, preprocO,
				astO, showTimeO, CIVLMacroO);
		CIVLCommand.addVerifyOrCompareOption(errorBoundO, verboseO, debugO,
				echoO, userIncludePathO, sysIncludePathO, showTransitionsO,
				showStatesO, showSavedStatesO, showQueriesO,
				showProverQueriesO, inputO, minO, mpiContractO, maxdepthO,
				procBoundO, saveStatesO, simplifyO, solveO, enablePrintfO,
				showAmpleSetO, showAmpleSetWtStatesO, statelessPrintfO,
				deadlockO, svcomp16O,pthreadOnlyO, showProgramO, showPathConditionO,
				ompNoSimplifyO, ompLoopDecompO, collectProcessesO,
				collectScopesO, collectHeapsO, macroO, preprocO, astO,
				showTimeO, showMemoryUnitsO, CIVLMacroO, showUnreachedCodeO,
				analyzeAbsO, collectOutputO, checkDivisionByZeroO,
				checkMemoryLeakO, timeoutO);
		CIVLCommand.addCompareOption(errorBoundO, verboseO, debugO, echoO,
				userIncludePathO, sysIncludePathO, showTransitionsO,
				showStatesO, showSavedStatesO, showQueriesO,
				showProverQueriesO, inputO, minO, maxdepthO, procBoundO,
				saveStatesO, simplifyO, solveO, enablePrintfO, showAmpleSetO,
				showAmpleSetWtStatesO, statelessPrintfO, deadlockO, svcomp16O,
				pthreadOnlyO,
				showProgramO, showPathConditionO, ompNoSimplifyO,
				ompLoopDecompO, collectProcessesO, collectScopesO,
				collectHeapsO, macroO, preprocO, astO, showTimeO,
				showMemoryUnitsO, CIVLMacroO, showUnreachedCodeO, analyzeAbsO,
				strictCompareO, checkDivisionByZeroO, checkMemoryLeakO,
				timeoutO);
		CIVLCommand.addReplayOption(showModelO, verboseO, debugO, echoO,
				showTransitionsO, showStatesO, showSavedStatesO, showQueriesO,
				showProverQueriesO, idO, traceO, enablePrintfO, showAmpleSetO,
				showAmpleSetWtStatesO, statelessPrintfO, guiO, showProgramO,
				showPathConditionO, preprocO, astO, showMemoryUnitsO,
				collectOutputO, checkDivisionByZeroO, checkMemoryLeakO);
		CIVLCommand.addRunOption(errorBoundO, verboseO, randomO, guidedO,
				seedO, debugO, echoO, userIncludePathO, sysIncludePathO,
				showTransitionsO, showStatesO, showSavedStatesO, showQueriesO,
				showProverQueriesO, inputO, maxdepthO, procBoundO, simplifyO,
				enablePrintfO, showAmpleSetO, showAmpleSetWtStatesO,
				statelessPrintfO, deadlockO, svcomp16O, pthreadOnlyO,showProgramO,
				showPathConditionO, ompNoSimplifyO, ompLoopDecompO,
				collectProcessesO, collectScopesO, collectHeapsO, macroO,
				preprocO, astO, showMemoryUnitsO, CIVLMacroO, collectOutputO,
				checkDivisionByZeroO, checkMemoryLeakO, timeoutO);
	}

	private static void addShowOption(Option... options) {
		for (Option option : options) {
			if (showOptions.containsKey(option.name()))
				throw new CIVLInternalException("Option " + option.name()
						+ " has already been added to show option map.",
						(CIVLSource) null);
			showOptions.put(option.name(), option);
		}
	}

	private static void addVerifyOrCompareOption(Option... options) {
		for (Option option : options) {
			if (verifyOptions.containsKey(option.name()))
				throw new CIVLInternalException("Option " + option.name()
						+ " has already been added to verify option map.",
						(CIVLSource) null);
			verifyOptions.put(option.name(), option);
		}
	}

	private static void addCompareOption(Option... options) {
		for (Option option : options) {
			if (compareOptions.containsKey(option.name()))
				throw new CIVLInternalException("Option " + option.name()
						+ " has already been added to compare option map.",
						(CIVLSource) null);
			compareOptions.put(option.name(), option);
		}
	}

	private static void addReplayOption(Option... options) {
		for (Option option : options) {
			if (replayOptions.containsKey(option.name()))
				throw new CIVLInternalException("Option " + option.name()
						+ " has already been added to replay option map.",
						(CIVLSource) null);
			replayOptions.put(option.name(), option);
		}
	}

	private static void addRunOption(Option... options) {
		for (Option option : options) {
			if (runOptions.containsKey(option.name()))
				throw new CIVLInternalException("Option " + option.name()
						+ " has already been added to run option map.",
						(CIVLSource) null);
			runOptions.put(option.name(), option);
		}
	}

	public static void printOptionsOfCommand(String command, PrintStream out) {
		switch (command) {
		case CommandLine.COMPARE:
			printOptions(verifyOptions.values(), out);
			break;
		case CommandLine.VERIFY:
			printOptions(verifyOptions.values(), out);
			break;
		case CommandLine.REPLAY:
			printOptions(replayOptions.values(), out);
			break;
		case CommandLine.RUN:
			printOptions(runOptions.values(), out);
			break;
		case CommandLine.SHOW:
			printOptions(showOptions.values(), out);
			break;
		case CommandLine.GUI:
		case CommandLine.CONFIG: // no options for "civl config"
		default:
		}
	}

	private static void printOptions(Collection<Option> options, PrintStream out) {
		for (Option option : options)
			out.println(option);
	}

	public static boolean isValid(CommandLine commandLine, Option option) {
		CommandLineKind kind = commandLine.commandLineKind();

		if (kind == CommandLineKind.NORMAL) {
			NormalCommandLine cmd = (NormalCommandLine) commandLine;
			NormalCommandKind cmdKind = cmd.normalCommandKind();

			switch (cmdKind) {
			case SHOW:
				return showOptions.containsKey(option.name());
			case VERIFY:
				return verifyOptions.containsKey(option.name());
			case REPLAY:
			case RUN:
				return replayOptions.containsKey(option.name());
			case CONFIG:
				return false; // no options for "civl config"
			default:
				return false;
			}
		} else {
			return verifyOptions.containsKey(option.name());
		}
	}

	public static SortedMap<String, Option> getReplayOptions() {
		return replayOptions;
	}

	public static SortedMap<String, Option> getRunOptions() {
		return runOptions;
	}

	public static SortedMap<String, Option> getShowOptions() {
		return showOptions;
	}

	public static SortedMap<String, Option> getVerifyOrCompareOptions() {
		return verifyOptions;
	}
}
