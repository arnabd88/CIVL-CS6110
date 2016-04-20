package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPI_OpenMPTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File("examples", "mpi-omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void pie() throws ABCException {
		assertTrue(ui.run(
				"verify -enablePrintf=false -DMATH_ELABORATE_ASSUMPTIONS -input_mpi_nprocs=2 "
						+ "-input_omp_thread_max=3 -ompLoopDecomp=ALL",
						TestConstants.QUIET, filename("mpi-omp-pie-calculation.c")));
	}

	@Test
	public void pie100() throws ABCException {
		assertTrue(ui
				.run("verify -enablePrintf=false -DMATH_ELABORATE_ASSUMPTIONS "
						+ "-input_mpi_nprocs=2 -input_omp_thread_max=10 -ompLoopDecomp=ALL",
						TestConstants.QUIET, filename("mpi-omp-pie-calculation100.c")));
	}

	@Test
	public void helloworld() throws ABCException {
		assertTrue(ui.run("verify -enablePrintf=false -input_mpi_nprocs=2",
				TestConstants.QUIET, filename("mpi-omp-hello-world.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
