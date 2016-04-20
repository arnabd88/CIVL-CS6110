package edu.udel.cis.vsl.abc;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * Tests pruner.
 * 
 * @author siegel
 * 
 */
public class PruneTest {

	public final static PrintStream out = System.out;

	public final static boolean debug = false;

	private File root = new File("examples/prune");

	private static Configuration config = Configurations
			.newMinimalConfiguration();

	private static FrontEnd fe = new FrontEnd(config);

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	private void check(File[] inputs, File oracle)
			throws PreprocessorException, SyntaxException, ParseException {
		Program program = fe.compileAndLink(inputs, Language.C);
		AST actual, expected;

		program.applyTransformer("prune");
		actual = program.getAST();
		expected = fe.compile(oracle, Language.C);
		if (debug) {
			expected.prettyPrint(out, false);
			out.println();
			actual.prettyPrint(out, false);
		}
		assertTrue(actual.getRootNode().equiv(expected.getRootNode()));
	}

	private void check(String[] inputNames, String oracleName)
			throws ABCException {
		File[] inputs = new File[inputNames.length];
		File oracle;

		for (int i = 0; i < inputs.length; i++)
			inputs[i] = new File(root, inputNames[i]);
		oracle = new File(root, oracleName);
		check(inputs, oracle);

	}

	@Test
	public void structs1() throws ABCException {
		check(new String[] { "structs1.c" }, "structs1_pruned.c");
	}

}
