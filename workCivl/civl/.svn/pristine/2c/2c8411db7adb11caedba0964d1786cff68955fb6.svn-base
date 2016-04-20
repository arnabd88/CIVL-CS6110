package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class HybridTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File("examples");

	private static UserInterface ui = new UserInterface();

	private static final String mpiOmp = "mpi-omp";

	// private static final String cudaOmp = "cuda-omp";

	/* *************************** Helper Methods *************************** */

	private static String filename(String parent, String name) {
		return new File(new File(rootDir, parent), name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void inform_blkstp() throws ABCException {
		assertTrue(ui.run(
				"verify -input_NPROCS=2 -inputTHREAD_MAX=2 -showTransitions=false "
						+ "-showAmpleSet -showSavedStates=false",
				filename(mpiOmp, "mpi-omp-mat-infnorm-blkstp.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
