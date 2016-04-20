package edu.udel.cis.vsl.civl.run.common;

import java.math.BigInteger;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

import org.antlr.v4.runtime.misc.NotNull;

import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.run.IF.CommandLine;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandLineKind;
import edu.udel.cis.vsl.civl.run.common.NormalCommandLine.NormalCommandKind;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.GMCSection;
import edu.udel.cis.vsl.gmc.Option;
import edu.udel.cis.vsl.gmc.Option.OptionType;

public class CIVLCommandListener extends CommandBaseListener implements
		CommandListener {

	// Instance fields...

	CommandLineKind kind;
	private String commandString;
	NormalCommandLine normalCmd = null;
	CompareCommandLine compareCmd = null;
	private GMCConfiguration gmcConfig;
	private GMCSection cmdSection;
	private List<String> files;

	/**
	 * Map of all options associated to this parser: key is name of option,
	 * value is the option.
	 */
	private SortedMap<String, Option> optionMap = new TreeMap<>();

	/**
	 * Map of all options of Map type associated to this parser. The entries of
	 * this map are a subset of those of {@link #optionMap}.
	 */
	private Map<String, Option> mapOptionMap = new LinkedHashMap<>();

	public CIVLCommandListener(String commandString, Collection<Option> options) {
		this.commandString = commandString;
		for (Option option : options) {
			String name = option.name();

			if (optionMap.put(name, option) != null)
				throw new IllegalArgumentException("Saw two options named "
						+ name);
			if (option.type() == OptionType.MAP)
				mapOptionMap.put(name, option);
		}
		gmcConfig = new GMCConfiguration(options);
	}

	@Override
	public void enterConfig(@NotNull CommandParser.ConfigContext ctx) {
		kind = CommandLineKind.NORMAL;
		normalCmd = new NormalCommandLine();
		normalCmd.setCommandString(this.commandString);
		normalCmd.setCommand(NormalCommandKind.CONFIG);
	}

	@Override
	public void enterHelp(@NotNull CommandParser.HelpContext ctx) {
		String commandArg = null;
		HelpCommandLine helpCmd = new HelpCommandLine();

		kind = CommandLineKind.NORMAL;
		helpCmd.setCommandString(this.commandString);
		helpCmd.setCommand(NormalCommandKind.HELP);
		if (ctx.children.size() > 2)
			commandArg = ctx.children.get(1).getText();
		if (commandArg != null) {
			switch (commandArg) {
			case CommandLine.COMPARE:
			case CommandLine.GUI:
			case CommandLine.HELP:
			case CommandLine.REPLAY:
			case CommandLine.RUN:
			case CommandLine.SHOW:
			case CommandLine.CONFIG:
			case CommandLine.VERIFY:
				helpCmd.setArg(commandArg);
				break;
			default:
				throw new RuntimeCommandException("invalid argument for help: "
						+ commandArg);
			}
		}
		normalCmd = helpCmd;
	}

	@Override
	public void enterNormal(@NotNull CommandParser.NormalContext ctx) {
		String cmdString = ctx.COMMAND() != null ? ctx.COMMAND().getText()
				: ctx.REPLAY().getText();

		kind = CommandLineKind.NORMAL;
		normalCmd = new NormalCommandLine();
		normalCmd.setCommandString(this.commandString);
		this.cmdSection = new GMCSection(GMCConfiguration.ANONYMOUS_SECTION);
		this.gmcConfig.setAnonymousSection(cmdSection);
		switch (cmdString) {
		case "verify":
			normalCmd.setCommand(NormalCommandKind.VERIFY);
			break;
		case "run":
			normalCmd.setCommand(NormalCommandKind.RUN);
			break;
		case "replay":
			normalCmd.setCommand(NormalCommandKind.REPLAY);
			break;
		case "show":
			normalCmd.setCommand(NormalCommandKind.SHOW);
			break;
		case "config":
			normalCmd.setCommand(NormalCommandKind.CONFIG);
			break;
		default: // TODO: why is this default?...
			normalCmd.setCommand(NormalCommandKind.GUI);
		}
	}

	@Override
	public void enterCompare(@NotNull CommandParser.CompareContext ctx) {
		kind = CommandLineKind.COMPARE;
		compareCmd = new CompareCommandLine(false);
		compareCmd.setCommandString(this.commandString);
	}

	@Override
	public void enterReplayCompare(
			@NotNull CommandParser.ReplayCompareContext ctx) {
		kind = CommandLineKind.COMPARE;
		compareCmd = new CompareCommandLine(true);
		compareCmd.setCommandString(this.commandString);
	}

	@Override
	public void enterSpecCommand(@NotNull CommandParser.SpecCommandContext ctx) {
		this.normalCmd = new NormalCommandLine();
		this.cmdSection = new GMCSection(CompareCommandLine.SPEC);
		this.gmcConfig.addSection(cmdSection);
	}

	@Override
	public void enterImplCommand(@NotNull CommandParser.ImplCommandContext ctx) {
		this.normalCmd = new NormalCommandLine();
		this.cmdSection = new GMCSection(CompareCommandLine.IMPL);
		this.gmcConfig.addSection(cmdSection);
	}

	@Override
	public void enterCommonOption(@NotNull CommandParser.CommonOptionContext ctx) {
		this.cmdSection = new GMCSection(GMCConfiguration.ANONYMOUS_SECTION);
		this.gmcConfig.setAnonymousSection(cmdSection);
	}

	@Override
	public void enterCommandBody(@NotNull CommandParser.CommandBodyContext ctx) {
		this.files = new LinkedList<>();
	}

	@Override
	public void enterNormalOption(@NotNull CommandParser.NormalOptionContext ctx) {
		String optionName = ctx.OPTION_NAME().getText().substring(1);
		Option option = optionMap.get(optionName);

		try {
			if (ctx.value() != null) {
				Object value = this.translateValue(option, ctx.value());

				cmdSection.setScalarValue(option, value);
			} else if (option.type() == OptionType.BOOLEAN)
				cmdSection.setScalarValue(option, true);
		} catch (IllegalArgumentException illegalArg) {
			throw new RuntimeCommandException(illegalArg.getMessage());
		}
	}

	private Object translateValue(Option option,
			@NotNull CommandParser.ValueContext ctx) {
		if (ctx.VAR() != null) {
			return ctx.VAR().getText();
		} else if (ctx.BOOLEAN() != null) {
			if (ctx.BOOLEAN().getText().equals("true"))
				return true;
			else
				return false;
		} else if (ctx.NUMBER() != null) {
			// NUMBER
			String optionName = option.name();

			if (optionName.equals(CIVLConstants.SEED)
					|| optionName.equals(CIVLConstants.INPUT))
				return new BigInteger(ctx.NUMBER().getText());
			else
				return Integer.parseInt(ctx.NUMBER().getText());
		} else if (ctx.PATH() != null)
			// PATH
			return ctx.PATH().getText();
		else {
			// STRING
			String whole = ctx.STRING().getText();

			return whole.substring(1, whole.length() - 1);
		}
	}

	@Override
	public void enterInputOption(@NotNull CommandParser.InputOptionContext ctx) {
		Option option = mapOptionMap.get(CIVLConstants.INPUT);
		String key = ctx.VAR().getText();
		Object value = this.translateValue(option, ctx.value());

		cmdSection.putMapEntry(option, key, value);
	}

	@Override
	public void enterMacroOption(@NotNull CommandParser.MacroOptionContext ctx) {
		Option option = mapOptionMap.get(CIVLConstants.MACRO);
		String name = ctx.VAR().getText();
		String value = ctx.value() != null ? ctx.value().getText() : "";

		cmdSection.putMapEntry(option, name, value);
	}

	@Override
	public void enterFile(@NotNull CommandParser.FileContext ctx) {
		String file = ctx.PATH().getText();

		this.cmdSection.addFreeArg(file);
		this.files.add(file);
	}

	// private void checkOptionInCommand(Option option) {
	// if (this.kind == CommandLineKind.NORMAL) {
	// CIVLCommand.isValid(commonCmd, option);
	// } else {
	// CIVLCommand.isValid(this.compareCmd, option);
	// }
	// }

	@Override
	public void exitNormal(@NotNull CommandParser.NormalContext ctx) {
		normalCmd.complete();
	}

	@Override
	public void exitCommandBody(@NotNull CommandParser.CommandBodyContext ctx) {
		this.normalCmd.setFiles(this.files);
		this.normalCmd.setGMCSection(this.cmdSection);
		this.normalCmd.setGMCConfig(this.gmcConfig);
	}

	@Override
	public void exitSpecCommand(@NotNull CommandParser.SpecCommandContext ctx) {
		this.normalCmd.complete();
		this.compareCmd.setSpecification(this.normalCmd);
	}

	@Override
	public void exitImplCommand(@NotNull CommandParser.ImplCommandContext ctx) {
		this.normalCmd.complete();
		this.compareCmd.setImplemenation(this.normalCmd);
	}

	@Override
	public void exitCompare(@NotNull CommandParser.CompareContext ctx) {
		compareCmd.setGMCConfig(gmcConfig);
	}

	@Override
	public void exitReplayCompare(
			@NotNull CommandParser.ReplayCompareContext ctx) {
		compareCmd.setGMCConfig(gmcConfig);
	}
}
