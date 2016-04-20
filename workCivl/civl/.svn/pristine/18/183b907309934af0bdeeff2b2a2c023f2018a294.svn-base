package edu.udel.cis.vsl.civl.run.common;

import java.io.PrintStream;
import java.util.Collection;
import java.util.SortedMap;
import java.util.TreeMap;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.run.IF.CommandLine;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandKind;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandLineKind;
import edu.udel.cis.vsl.civl.run.common.NormalCommandLine.NormalCommandKind;
import edu.udel.cis.vsl.gmc.Option;

public class CIVLCommand {

	// public final static SortedMap<String, Option> definedOptions = new
	// TreeMap<>();

	private static SortedMap<String, Option> showOptions = new TreeMap<>();
	private static SortedMap<String, Option> verifyOrCompareOptions = new TreeMap<>();
	private static SortedMap<String, Option> replayOptions = new TreeMap<>();
	private static SortedMap<String, Option> runOptions = new TreeMap<>();

	public static void addShowOption(Option... options) {
		for (Option option : options) {
			if (showOptions.containsKey(option.name()))
				throw new CIVLInternalException("Option " + option.name()
						+ " has already been added to show option map.",
						(CIVLSource) null);
			showOptions.put(option.name(), option);
		}
	}

	public static void addVerifyOrCompareOption(Option... options) {
		for (Option option : options) {
			if (verifyOrCompareOptions.containsKey(option.name()))
				throw new CIVLInternalException(
						"Option "
								+ option.name()
								+ " has already been added to verify/compare option map.",
						(CIVLSource) null);
			verifyOrCompareOptions.put(option.name(), option);
		}
	}

	public static void addReplayOption(Option... options) {
		for (Option option : options) {
			if (replayOptions.containsKey(option.name()))
				throw new CIVLInternalException("Option " + option.name()
						+ " has already been added to replay option map.",
						(CIVLSource) null);
			replayOptions.put(option.name(), option);
		}
	}

	public static void addRunOption(Option... options) {
		for (Option option : options) {
			if (runOptions.containsKey(option.name()))
				throw new CIVLInternalException("Option " + option.name()
						+ " has already been added to run option map.",
						(CIVLSource) null);
			runOptions.put(option.name(), option);
		}
	}

	public static void printOptionsOfCommand(CommandKind command,
			PrintStream out) {
		switch (command) {
		case COMPARE:
		case VERIFY:
			printOptions(verifyOrCompareOptions.values(), out);
			break;
		case REPLAY:
			printOptions(replayOptions.values(), out);
			break;
		case RUN:
			printOptions(runOptions.values(), out);
			break;
		case SHOW:
			printOptions(showOptions.values(), out);
			break;
		case GUI:
		case CONFIG: // no options for "civl config"
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
				return verifyOrCompareOptions.containsKey(option.name());
			case REPLAY:
			case RUN:
				return replayOptions.containsKey(option.name());
			case CONFIG:
				return false; // no options for "civl config"
			default:
				return false;
			}
		} else {
			return verifyOrCompareOptions.containsKey(option.name());
		}
	}
}
