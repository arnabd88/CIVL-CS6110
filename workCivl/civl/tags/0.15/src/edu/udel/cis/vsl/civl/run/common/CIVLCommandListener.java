package edu.udel.cis.vsl.civl.run.common;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

import org.antlr.v4.runtime.misc.NotNull;

import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandKind;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandLineKind;
import edu.udel.cis.vsl.civl.run.common.NormalCommandLine.NormalCommandKind;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.Option;
import edu.udel.cis.vsl.gmc.Option.OptionType;

public class CIVLCommandListener extends CommandBaseListener implements
		CommandListener {

	CommandLineKind kind;
	private String commandString;
	NormalCommandLine normalCmd = null;
	CompareCommandLine compareCmd = null;
	private GMCConfiguration commonConfig = null, config;
	private List<String> files;

	// Instance fields...

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
	}

	@Override
	public void enterHelp(@NotNull CommandParser.HelpContext ctx) {
		String commandArg = null;
		
		kind = CommandLineKind.NORMAL;
		normalCmd = new NormalCommandLine();
		normalCmd.setCommandString(this.commandString);
		normalCmd.setCommand(NormalCommandKind.HELP);
		if(ctx.children.size() > 2)
			commandArg = ctx.children.get(1).getText();
		if (commandArg != null) {
//			String commandArg = ctx.COMMAND().getText();
			switch (commandArg) {
			case "compare":
				normalCmd.setCommandArg(CommandKind.COMPARE);
				break;
			case "gui":
				normalCmd.setCommandArg(CommandKind.GUI);
				break;
			case "help":
				normalCmd.setCommandArg(CommandKind.HELP);
				break;
			case "replay":
				normalCmd.setCommandArg(CommandKind.REPLAY);
				break;
			case "run":
				normalCmd.setCommandArg(CommandKind.RUN);
				break;
			case "show":
				normalCmd.setCommandArg(CommandKind.SHOW);
				break;
			default:
				normalCmd.setCommandArg(CommandKind.VERIFY);
			}
		}
	}

	@Override
	public void enterNormal(@NotNull CommandParser.NormalContext ctx) {
		String cmdString = ctx.COMMAND() != null ? ctx.COMMAND().getText()
				: ctx.REPLAY().getText();

		kind = CommandLineKind.NORMAL;
		normalCmd = new NormalCommandLine();
		normalCmd.setCommandString(this.commandString);
		this.config = new GMCConfiguration(optionMap.values());

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
		default: //
			normalCmd.setCommand(NormalCommandKind.GUI);
		}
	}

	@Override
	public void enterCompare(@NotNull CommandParser.CompareContext ctx) {
		kind = CommandLineKind.COMPARE;
		compareCmd = new CompareCommandLine(false);
		compareCmd.setCommandString(this.commandString);
		this.config = new GMCConfiguration(optionMap.values());
	}

	@Override
	public void enterReplayCompare(
			@NotNull CommandParser.ReplayCompareContext ctx) {
		kind = CommandLineKind.COMPARE;
		compareCmd = new CompareCommandLine(true);
		compareCmd.setCommandString(this.commandString);
		this.config = new GMCConfiguration(optionMap.values());
	}

	@Override
	public void enterSpecCommand(@NotNull CommandParser.SpecCommandContext ctx) {
		this.normalCmd = new NormalCommandLine();
		if (this.commonConfig == null)
			this.commonConfig = this.config;
		this.config = this.commonConfig.clone();
	}

	@Override
	public void enterImplCommand(@NotNull CommandParser.ImplCommandContext ctx) {
		this.normalCmd = new NormalCommandLine();
		if (this.commonConfig == null)
			this.commonConfig = this.config;
		this.config = this.commonConfig.clone();
	}

	@Override
	public void enterCommandBody(@NotNull CommandParser.CommandBodyContext ctx) {
		this.files = new LinkedList<>();
	}

	@Override
	public void enterNormalOption(@NotNull CommandParser.NormalOptionContext ctx) {
		String optionName = ctx.OPTION_NAME().getText().substring(1);
		Option option = optionMap.get(optionName);

		if (ctx.value() != null) {
			Object value = this.translateValue(ctx.value());

			config.setScalarValue(option, value);
		} else if (option.type() == OptionType.BOOLEAN)
			config.setScalarValue(option, true);
	}

	private Object translateValue(@NotNull CommandParser.ValueContext ctx) {
		if (ctx.VAR() != null) {
			return ctx.VAR().getText();
		} else if (ctx.BOOLEAN() != null) {
			if (ctx.BOOLEAN().getText().equals("true"))
				return true;
			else
				return false;
		} else if(ctx.NUMBER() != null) {
			// NUMBER
			return Integer.parseInt(ctx.NUMBER().getText());
		}else //PATH
			return ctx.PATH().getText();
	}

	@Override
	public void enterInputOption(@NotNull CommandParser.InputOptionContext ctx) {
		Option option = mapOptionMap.get("input");
		String key = ctx.VAR().getText();
		Object value = this.translateValue(ctx.value());

		config.putMapEntry(option, key, value);
	}

	@Override
	public void enterMacroOption(@NotNull CommandParser.MacroOptionContext ctx) {
		Option option = mapOptionMap.get("D");
		String name = ctx.VAR().getText();
		String value = ctx.value() != null ? ctx.value().getText() : "";

		config.putMapEntry(option, name, value);
	}

	@Override
	public void enterFile(@NotNull CommandParser.FileContext ctx) {
		String file = ctx.PATH().getText();

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
		this.normalCmd.setConfiguration(this.config);
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
}
