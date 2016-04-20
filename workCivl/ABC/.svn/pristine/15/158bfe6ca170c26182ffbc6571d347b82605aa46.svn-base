package edu.udel.cis.vsl.abc.parse;

import java.io.File;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import org.junit.Test;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class ACSLTest {

	private boolean debug = false;
	private static PrintStream out = System.out;
	@SuppressWarnings("unused")
	private static Map<String, Macro> implicitMacros = new HashMap<>();
	@SuppressWarnings("unused")
	private static File[] systemIncludes = new File[0];
	@SuppressWarnings("unused")
	private static File[] userIncludes = new File[0];
	private static File root = new File(new File("examples"), "contract");
	private static Configuration config = Configurations
			.newMinimalConfiguration();

	private static FrontEnd frontEnd = new FrontEnd(config);

	private void parse(String name) throws PreprocessorException,
			SyntaxException, ParseException {
		File file = new File(root, name);
		AST result;

		// tokens = preprocessor.outputTokenSource(systemIncludes, userIncludes,
		// implicitMacros, file);
		result = frontEnd.compile(file, Language.CIVL_C);
		if (debug) {
			result.print(out);
			// result.prettyPrint(out, true);
			out.println();
			out.flush();
		}
	}

	@Test
	public void example1() throws PreprocessorException, SyntaxException,
			ParseException {
		this.parse("acslDemo.c");
	}

	@Test
	public void cqueue() throws PreprocessorException, SyntaxException,
			ParseException {
		this.parse("cqueue.c");
	}

	@Test
	public void mpiCollective() throws PreprocessorException, SyntaxException,
			ParseException {
		this.parse("mpiCollectiveTest.c");
	}

	@Test
	public void mpiConstants() throws PreprocessorException, SyntaxException,
			ParseException {
		this.parse("mpiConstants.c");
	}

	@Test
	public void wildcard() throws PreprocessorException, SyntaxException,
			ParseException {
		this.parse("wildcard_contract_bad.c");
	}

	@Test
	public void emptyInBad() throws PreprocessorException, SyntaxException,
			ParseException {
		this.parse("isRecvBufEmpty_BAD.c");
	}

	@Test
	public void emptyInOk() throws PreprocessorException, SyntaxException,
			ParseException {
		this.parse("isRecvBufEmpty_OK.c");
	}

	@Test
	public void loopInvariant() throws PreprocessorException, SyntaxException,
			ParseException {
		this.parse("loopInvariant.c");
	}

	@Test
	public void validPointers() throws PreprocessorException, SyntaxException,
			ParseException {
		// this.parse("valid.c");
		parse("validPointers.c");
	}

	@Test
	public void remoteAccess() throws PreprocessorException, SyntaxException,
			ParseException {
		// this.parse("valid.c");
		parse("remoteAccess.c");
	}

	@Test
	public void memLocation1() throws PreprocessorException, SyntaxException,
			ParseException {
		this.parse("memLocation1.c");
	}
}
