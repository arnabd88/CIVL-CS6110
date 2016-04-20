package edu.udel.cis.vsl.civl.run.common;

import java.util.BitSet;
import java.util.Collection;

import org.antlr.v4.runtime.ANTLRErrorListener;
import org.antlr.v4.runtime.ANTLRErrorStrategy;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import edu.udel.cis.vsl.civl.run.IF.CommandLine;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandLineKind;
import edu.udel.cis.vsl.gmc.CommandLineException;
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
			String... args) throws CommandLineException {
		ANTLRErrorListener myErrorListener = new MyErrorListener();
		ANTLRErrorStrategy myHandler = new MyErrorStrategy();

		String command = args2Command(args);

		try {
			ANTLRInputStream input = new ANTLRInputStream(command);
			// System.out.println("create lexer...");
			CommandLexer lexer = new CommandLexer(input);
			// System.out.println("create token stream...");

			lexer.removeErrorListeners();
			lexer.addErrorListener(myErrorListener);

			CommonTokenStream tokens = new CommonTokenStream(lexer);
			// System.out.println("create parser...");
			CommandParser parser = new CommandParser(tokens);
			// System.out.println("create parser tree...");

			parser.removeErrorListeners();
			parser.setErrorHandler(myHandler);

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
		} catch (RuntimeCommandException e) {
			throw new CommandLineException(e.getMessage());
		}
	}
}

class MyErrorListener implements ANTLRErrorListener {

	@Override
	public void reportAmbiguity(Parser arg0, DFA arg1, int arg2, int arg3,
			boolean arg4, BitSet arg5, ATNConfigSet arg6) {
		throw new RuntimeCommandException();
	}

	@Override
	public void reportAttemptingFullContext(Parser arg0, DFA arg1, int arg2,
			int arg3, BitSet arg4, ATNConfigSet arg5) {
		throw new RuntimeCommandException();
	}

	@Override
	public void reportContextSensitivity(Parser arg0, DFA arg1, int arg2,
			int arg3, int arg4, ATNConfigSet arg5) {
		throw new RuntimeCommandException();
	}

	@Override
	public void syntaxError(Recognizer<?, ?> arg0, Object arg1, int arg2,
			int arg3, String arg4, RecognitionException arg5) {
		throw new RuntimeCommandException(arg5.getMessage());
	}

}

class MyErrorStrategy implements ANTLRErrorStrategy {

	@Override
	public boolean inErrorRecoveryMode(Parser arg0) {
		return false;
	}

	@Override
	public void recover(Parser arg0, RecognitionException arg1)
			throws RecognitionException {
	}

	@Override
	public Token recoverInline(Parser arg0) throws RecognitionException {
		throw new RuntimeCommandException();
	}

	@Override
	public void reportError(Parser arg0, RecognitionException arg1) {
		throw new RuntimeCommandException("Command line syntax error at "
				+ arg1.getOffendingToken().toString());
	}

	@Override
	public void reportMatch(Parser arg0) {
	}

	@Override
	public void reset(Parser arg0) {
	}

	@Override
	public void sync(Parser arg0) throws RecognitionException {
	}
}
