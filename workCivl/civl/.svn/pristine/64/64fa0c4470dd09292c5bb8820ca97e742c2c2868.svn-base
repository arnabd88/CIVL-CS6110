package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPI_OpenMPDevTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File("examples", "mpi-omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void matmat_mw() throws ABCException {
		assertTrue(ui
				.run("verify -input_omp_thread_max=2 -enablePrintf=false -showTransitions=false",
						filename("matmat_mw.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
