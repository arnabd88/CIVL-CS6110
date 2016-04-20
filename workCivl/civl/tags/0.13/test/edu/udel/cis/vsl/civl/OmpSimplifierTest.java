package edu.udel.cis.vsl.civl;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.FrontEnd;
import edu.udel.cis.vsl.abc.config.IF.Configuration.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.civl.transform.IF.CIVLTransform;

public class OmpSimplifierTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private static File[] systemIncludes = new File[0];

	private static File[] userIncludes = new File[0];

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
		File file = new File(rootDir, fileNameRoot + ".c");
		File simplifiedFile = new File(new File(rootDir, "simple"),
				fileNameRoot + ".c.s");

		Program program, simplifiedProgram;

		{ // Parse the program and apply the CIVL transformations
			program = frontEnd.compileAndLink(new File[] { file },
					Language.CIVL_C, systemIncludes, userIncludes);
			program.applyTransformer(CIVLTransform.OMP_SIMPLIFY);
		}

		{ // Parse the simplified program
			simplifiedProgram = frontEnd.compileAndLink(
					new File[] { simplifiedFile }, Language.CIVL_C,
					systemIncludes, userIncludes);
		}

		if (!program.getAST().getRootNode()
				.equiv(simplifiedProgram.getAST().getRootNode())) {
			out.println("For " + fileNameRoot
					+ " expected simplified version to be:");
			frontEnd.printProgram(out, simplifiedProgram, false, false);
			out.println("Computed simplified version was:");
			program.getAST().prettyPrint(out, true);
			assert false;
		}
	}

	/* **************************** Test Methods *************************** */

	@Ignore
	@Test
	public void dotProduct_critical1() throws ABCException, IOException {
		check("dotProduct_critical");
	}

	@Ignore
	@Test
	public void nested() throws ABCException, IOException {
		check("nested");
	}

	@Ignore
	@Test
	public void dotProduct_critical() throws ABCException, IOException {
		check("dotProduct_critical");
	}

	@Ignore
	@Test
	public void dotProduct_orphan() throws ABCException, IOException {
		check("dotProduct_orphan");
	}

	@Ignore
	@Test
	public void dotProduct1() throws ABCException, IOException {
		check("dotProduct1");
	}

	@Ignore
	@Test
	public void matProduct1() throws ABCException, IOException {
		check("matProduct1");
	}

	@Ignore
	@Test
	public void matProduct2() throws ABCException, IOException {
		check("matProduct2");
	}

	@Ignore
	@Test
	public void raceCond1() throws ABCException, IOException {
		check("raceCond1");
	}

	@Ignore
	@Test
	public void raceCond2() throws ABCException, IOException {
		check("raceCond2");
	}

	@Ignore
	@Test
	public void vecAdd_deadlock() throws ABCException, IOException {
		check("vecAdd_deadlock");
	}

	@Ignore
	@Test
	public void vecAdd_fix() throws ABCException, IOException {
		check("vecAdd_fix");
	}

	@Ignore
	@Test
	public void fig310_mxv_omp() throws ABCException, IOException {
		check("fig3.10-mxv-omp");
	}

	@Ignore
	@Test
	public void fig498_threadprivate() throws ABCException, IOException {
		check("fig4.98-threadprivate");
	}

	@Ignore
	@Test
	public void parallelfor() throws ABCException, IOException {
		check("parallelfor");
	}

	@Ignore
	@Test
	public void dijkstra() throws ABCException, IOException {
		check("dijkstra_openmp");
	}

	@Ignore
	@Test
	public void fft() throws ABCException, IOException {
		check("fft_openmp");
	}

	@Ignore
	@Test
	public void md() throws ABCException, IOException {
		check("md_openmp");
	}

	@Ignore
	@Test
	public void poisson() throws ABCException, IOException {
		check("poisson_openmp");
	}

	@Ignore
	@Test
	public void quad() throws ABCException, IOException {
		check("quad_openmp");
	}
}
