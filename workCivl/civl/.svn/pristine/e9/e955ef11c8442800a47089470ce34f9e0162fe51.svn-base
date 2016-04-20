package edu.udel.cis.vsl.civl;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.FrontEnd;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.config.IF.Configuration.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;
import edu.udel.cis.vsl.civl.transform.IF.TransformerFactory;
import edu.udel.cis.vsl.civl.transform.IF.Transforms;

public class OmpSimplifierTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private PrintStream out = System.out;

	/* *************************** Helper Methods ************************** */

	/*
	 * check whether the result of running the OMP simplifier is equivalent to
	 * the expected output, which is stored as a file with an added suffix of
	 * ".s" in the subdirectory "examples/simple".
	 * 
	 * @param filenameRoot The file name of the OpenMP program (without
	 * extension).
	 * 
	 * @throws ABCException
	 * 
	 * @throws IOException
	 */
	private void check(String fileNameRoot) throws ABCException, IOException {
		FrontEnd frontEnd = new FrontEnd();
		TransformerFactory transformerFactory = Transforms
				.newTransformerFactory(frontEnd.getASTFactory());
		File file = new File(rootDir, fileNameRoot + ".c");
		File simplifiedFile = new File(new File(rootDir, "simple"),
				fileNameRoot + ".c.s");
		@SuppressWarnings("unused")
		Program program, simplifiedProgram;
		@SuppressWarnings("unused")
		DifferenceObject diff;

		{ // Parse the program and apply the CIVL transformations
			program = frontEnd.compileAndLink(new File[] { file },
					Language.CIVL_C);
			program.apply(transformerFactory.getOpenMPSimplifier());
			out.println("DEBUG: simplified program is ...");
			program.getAST().prettyPrint(out, true);
		}

		{ // Parse the simplified program
			simplifiedProgram = frontEnd.compileAndLink(
					new File[] { simplifiedFile }, Language.CIVL_C);
		}
		/*diff = program.getAST().getRootNode()
				.diff(simplifiedProgram.getAST().getRootNode());
		if (diff != null) {
			out.println("For " + fileNameRoot
					+ " expected simplified version to be:");
			simplifiedProgram.getAST().prettyPrint(out, true);
			out.println("Computed simplified version was:");
			program.getAST().prettyPrint(out, true);
			out.println("Difference is: ");
			diff.print(out);
			assertTrue(false);
		}*/
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dotProduct_critical1() throws ABCException, IOException {
		check("dotProduct_critical");
	}

	@Test
	public void nested() throws ABCException, IOException {
		check("nested");
	}

	@Test
	public void dotProduct_critical() throws ABCException, IOException {
		check("dotProduct_critical");
	}

	@Test
	public void dotProduct_orphan() throws ABCException, IOException {
		check("dotProduct_orphan");
	}

	@Test
	public void dotProduct1() throws ABCException, IOException {
		check("dotProduct1");
	}

	@Test
	public void matProduct1() throws ABCException, IOException {
		check("matProduct1");
	}

	@Test
	public void matProduct2() throws ABCException, IOException {
		check("matProduct2");
	}

	@Test
	public void raceCond1() throws ABCException, IOException {
		check("raceCond1");
	}

	@Test
	public void raceCond2() throws ABCException, IOException {
		check("raceCond2");
	}

	@Test
	public void vecAdd_deadlock() throws ABCException, IOException {
		check("vecAdd_deadlock");
	}

	@Test
	public void vecAdd_fix() throws ABCException, IOException {
		check("vecAdd_fix");
	}

	@Test
	public void fig310_mxv_omp() throws ABCException, IOException {
		check("fig3.10-mxv-omp");
	}

	@Test
	public void fig498_threadprivate() throws ABCException, IOException {
		check("fig4.98-threadprivate");
	}

	@Test
	public void parallelfor() throws ABCException, IOException {
		check("parallelfor");
	}

	@Test
	public void dijkstra() throws ABCException, IOException {
		check("dijkstra_openmp");
	}

	@Test
	public void fft() throws ABCException, IOException {
		check("fft_openmp");
	}

	@Test
	public void md() throws ABCException, IOException {
		check("md_openmp");
	}

	@Test
	public void poisson() throws ABCException, IOException {
		check("poisson_openmp");
	}

	@Test
	public void quad() throws ABCException, IOException {
		check("quad_openmp");
	}
	
	@Test
	public void pi() throws ABCException, IOException {
		check("pi");
	}
	
	@Test
	public void region1() throws ABCException, IOException {
		check("region1");
	}
	
	@Test
	public void region2() throws ABCException, IOException {
		check("region2");
	}
	
	@Test
	public void defect_num_544() throws ABCException, IOException {
		check("defect_num_544");
	}

	@SuppressWarnings("unused")
	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	@SuppressWarnings("unused")
	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	/*@Ignore
	@Test
	public void dotProduct1Verify() {
		assertTrue(ui.run("verify", "-inputTHREAD_MAX=2",
				filename("dotProduct1.c")));
		assertTrue(ui.run("verify", "-ompNoSimplify", "-inputTHREAD_MAX=2",
				filename("dotProduct1.c")));
	}

	@Test
	public void dotProductCriticalVerify() {
		assertTrue(ui.run("verify", "-inputTHREAD_MAX=4",
				filename("dotProduct_critical.c")));
		assertTrue(ui.run("verify", "-ompNoSimplify", "-inputTHREAD_MAX=4",
				filename("dotProduct_critical.c")));
	}

	@Test
	public void matProduct1Verify() {
		assertTrue(ui.run("verify", "-inputTHREAD_MAX=4",
				filename("matProduct1.c")));
		assertTrue(ui.run("verify", "-ompNoSimplify", "-inputTHREAD_MAX=4",
				filename("matProduct1.c")));
	}

	@Ignore
	@Test
	public void parallelforVerify() {
		assertTrue(ui.run("verify", "-inputTHREAD_MAX=4",
				filename("parallelfor.c")));
		assertTrue(ui.run("verify", "-ompNoSimplify", "-inputTHREAD_MAX=4",
				filename("parallelfor.c")));
	}

	@Test
	public void raceCond1Verify() {
		assertTrue(ui.run("verify", "-inputTHREAD_MAX=4",
				filename("raceCond1.c")));
		assertTrue(ui.run("verify", "-ompNoSimplify", "-inputTHREAD_MAX=4",
				filename("raceCond1.c")));
	}*/
	
	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
