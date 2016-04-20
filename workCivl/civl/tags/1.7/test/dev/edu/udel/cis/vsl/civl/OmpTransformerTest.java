package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;
import edu.udel.cis.vsl.civl.transform.IF.TransformerFactory;
import edu.udel.cis.vsl.civl.transform.IF.Transforms;

public class OmpTransformerTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private static UserInterface ui = new UserInterface();

	private PrintStream out = System.out;

	private File root = new File(new File("examples"), "omp");

	// private static List<String> codes = Arrays.asList("prune", "sef");

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/**
	 * tests an OpenMP program by applying the following transformers in
	 * sequence:
	 * <ol>
	 * <li>OpenMP Pragma transformer;</li>
	 * <li>OpenMP to CIVL transformer;</li>
	 * <li>Pruner;</li>
	 * <li>Side Effect Remover.</li>
	 * </ol>
	 * 
	 * @param filenameRoot
	 *            The file name of the OpenMP program (without extension).
	 * @param debug
	 *            The flag to be set for printing.
	 * @throws ABCException
	 * @throws IOException
	 */
	private void check(String filenameRoot, boolean debug) throws ABCException,
			IOException {
		FrontEnd frontEnd = new FrontEnd(
				Configurations.newMinimalConfiguration());
		TransformerFactory transformerFactory = Transforms
				.newTransformerFactory(frontEnd.getASTFactory());
		Program program;
		File file = new File(root, filenameRoot + ".c");

		program = frontEnd.compileAndLink(new File[] { file }, Language.CIVL_C);
		if (debug) {
			PrintStream before = new PrintStream("/tmp/before_simplify");
			program.getAST().prettyPrint(before, true);
			PrintStream beforeAST = new PrintStream("/tmp/before_AST");
			frontEnd.printProgram(beforeAST, program, false, false);
		}
		program.apply(transformerFactory.getOpenMPSimplifier());
		if (debug) {
			PrintStream after = new PrintStream("/tmp/after_simplify");
			program.getAST().prettyPrint(after, true);
		}
		program.apply(transformerFactory.getOpenMP2CIVLTransformer(null));
		if (debug) {
			out.println("======== After applying OpenMP Simplifier ========");
			frontEnd.printProgram(out, program, true, false);
		}
		program.applyTransformer("prune");
		if (debug) {
			out.println("======== After applying Pruner ========");
			frontEnd.printProgram(out, program, true, false);
		}
		program.applyTransformer("sef");
		if (debug) {
			out.println("======== After applying Side Effect Remover ========");
			frontEnd.printProgram(out, program, true, false);
		}
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dotProduct_critical1_run() throws ABCException, IOException {
		assertTrue(ui.run("show", "-showModel",
				filename("dotProduct_critical.c")));
	}

	@Ignore
	@Test
	public void nested_run() throws ABCException, IOException {
		assertTrue(ui.run("show", "-showModel", filename("nested.c")));
	}

	@Test
	public void dotProduct_critical1() throws ABCException, IOException {
		check("dotProduct_critical", false);
	}

	@Test
	public void nested() throws ABCException, IOException {
		check("nested", false);
	}

	@Test
	public void dotProduct_critical() throws ABCException, IOException {
		check("dotProduct_critical", false);
	}

	@Test
	public void dotProduct_orphan() throws ABCException, IOException {
		check("dotProduct_orphan", false);
	}

	@Test
	public void dotProduct1() throws ABCException, IOException {
		check("dotProduct1", false);
	}

	@Test
	public void matProduct1() throws ABCException, IOException {
		check("matProduct1", false);
	}

	@Test
	public void matProduct2() throws ABCException, IOException {
		check("matProduct2", false);
	}

	@Test
	public void raceCond1() throws ABCException, IOException {
		check("raceCond1", false);
	}

	@Test
	public void raceCond2() throws ABCException, IOException {
		check("raceCond2", false);
	}

	@Test
	public void vecAdd_deadlock() throws ABCException, IOException {
		check("vecAdd_deadlock", false);
	}

	@Test
	public void vecAdd_fix() throws ABCException, IOException {
		check("vecAdd_fix", false);
	}

	@Test
	public void fig310_mxv_omp() throws ABCException, IOException {
		check("fig3.10-mxv-omp", false);
	}

	@Test
	public void fig498_threadprivate() throws ABCException, IOException {
		check("fig4.98-threadprivate", false);
	}

	@Test
	public void parallelfor() throws ABCException, IOException {
		check("parallelfor", false);
	}

	@Test
	public void dijkstra() throws ABCException, IOException {
		check("dijkstra_openmp", false);
	}

	@Test
	public void fft() throws ABCException, IOException {
		check("fft_openmp", false);
	}

	@Test
	public void md() throws ABCException, IOException {
		check("md_openmp", false);
	}

	@Test
	public void poisson() throws ABCException, IOException {
		check("poisson_openmp", false);
	}

	@Test
	public void quad() throws ABCException, IOException {
		check("quad_openmp", false);
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
