package edu.udel.cis.vsl.civl.run.common;

import java.util.Collection;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import edu.udel.cis.vsl.civl.run.IF.CommandLine;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandLineKind;
import edu.udel.cis.vsl.gmc.Option;

public class CIVLCommandFactory {

	private static String args2Command(String... args) {
		String cmd = "";

		for (String arg : args) {
			cmd = cmd + arg + " ";
		}
		cmd = cmd + "\n";
		return cmd;
	}

	public static CommandLine parseCommand(Collection<Option> options,
			String... args) {
		String command = args2Command(args);
		ANTLRInputStream input = new ANTLRInputStream(command);
		// System.out.println("create lexer...");
		CommandLexer lexer = new CommandLexer(input);
		// System.out.println("create token stream...");
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		// System.out.println("create parser...");
		CommandParser parser = new CommandParser(tokens);
		// System.out.println("create parser tree...");
		ParseTree tree = parser.start();
		ParseTreeWalker walker = new ParseTreeWalker();
		CIVLCommandListener translator = new CIVLCommandListener(command,
				options);

		// System.out.println("walking through CIVL command listener...");
		walker.walk(translator, tree);
		if (translator.kind == CommandLineKind.NORMAL)
			return translator.normalCmd;
		else
			return translator.compareCmd;
	}
}
