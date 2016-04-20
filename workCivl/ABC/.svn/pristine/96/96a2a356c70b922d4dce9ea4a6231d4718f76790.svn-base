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
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * Tests compilation of multiple translation units. All tests have the following
 * structure: (1) there is a sequence of n filenames which form the inputs, (2)
 * there is a single filename which is the test oracle, representing the result
 * of compiling and merging the n translation units. The test proceeds by
 * compiling and linking the input files, compiling the oracle, and then
 * checking the two resulting ASTs are equivalent.
 * 
 * @author siegel
 * 
 */
public class LinkTest {

	public final static PrintStream out = System.out;

	public final static boolean debug = false;

	private File root = new File(new File("examples"), "link");

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
		AST actual = fe.compileAndLink(inputs, Language.CIVL_C).getAST();
		AST expected = fe.compile(oracle, Language.CIVL_C);

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
	public void a() throws ABCException {
		check(new String[] { "a_0.c", "a_1.c", "a_2.c" }, "a.c");
	}

	@Test
	public void b() throws ABCException {
		check(new String[] { "b_0.c", "b_1.c" }, "b.c");
	}

	@Test
	public void c() throws ABCException {
		check(new String[] { "c_0.c", "c_1.c" }, "c.c");
	}

	@Test
	public void enum1() throws ABCException {
		check(new String[] { "enum1_0.c", "enum1_1.c" }, "enum1.c");
	}

	@Test
	public void enum2() throws ABCException {
		check(new String[] { "enum2_0.c", "enum2_1.c" }, "enum2.c");
	}

	@Test
	public void enum3() throws ABCException {
		check(new String[] { "enum3_0.c", "enum3_1.c" }, "enum3.c");
	}

	@Test
	public void enum4() throws ABCException {
		check(new String[] { "enum4_0.c", "enum4_1.c" }, "enum4.c");
	}

	@Test
	public void extern() throws ABCException {
		check(new String[] { "extern/var_0.c", "extern/var_1.c",
				"extern/var_2.c" }, "extern/var.c");
	}

	@Test
	public void struct_compat() throws ABCException {
		check(new String[] { "struct_compat_0.c", "struct_compat_1.c" },
				"struct_compat.c");
	}

	@Test
	public void struct_incompat() throws ABCException {
		check(new String[] { "struct_incompat_0.c", "struct_incompat_1.c" },
				"struct_incompat.c");
	}

	@Test
	public void struct4() throws ABCException {
		check(new String[] { "struct4_0.c", "struct4_1.c", "struct4_2.c",
				"struct4_3.c" }, "struct4.c");
	}

	@Test
	public void sys() throws ABCException {
		check(new String[] { "sys_0.cvl", "sys_1.cvl" }, "sys.cvl");
	}

	@Test
	public void typedef1() throws ABCException {
		check(new String[] { "typedef1_0.c", "typedef1_1.c" }, "typedef1.c");
	}

	@Test
	public void typedef2() throws ABCException {
		check(new String[] { "typedef2_0.c", "typedef2_1.c" }, "typedef2.c");
	}

	@Test
	public void enumconflict() throws ABCException {
		check(new String[] { "enumconflict_0.c", "enumconflict_1.c",
				"enumconflict_2.c" }, "enumconflict.c");
	}

	@Test
	public void structunion() throws ABCException {
		check(new String[] { "structunion_0.c", "structunion_1.c",
				"structunion_2.c" }, "structunion.c");
	}

	/**
	 * Tests linkage when there are two distinct quantified scopes with same
	 * variable name.
	 * 
	 * @throws ABCException
	 */
	@Test
	public void quantifier() throws ABCException {
		check(new String[] { "quantifier.cvl" }, "quantifier.cvl");
	}
}
