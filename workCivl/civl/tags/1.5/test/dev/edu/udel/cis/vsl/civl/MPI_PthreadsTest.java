package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPI_PthreadsTest {
	/* *************************** Static Fields *************************** */
	private static final String mpiPthread = "mpi-pthread";

	private static File rootDir = new File("examples", mpiPthread);

	private static UserInterface ui = new UserInterface();

	// private static final String cudaOmp = "cuda-omp";

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void mpipthreads_both() throws ABCException {
		assertTrue(ui.run("verify", "-input_NPROCS=2", "-showInputs=false",
				"-enablePrintf=false", "-enablePrintf=false",
				"-showTransitions=false", filename("mpithreads_both.c")));
	}

	@Test
	public void mpi_pthreads_pie_collective() throws ABCException {
		assertTrue(ui
				.run("verify",
						"-showModel=false -showProgram=false -input_NPROCS=2 -inputNUM_INTERVAL_BOUND=3",
						"-enablePrintf=false",
						filename("mpi-pthreads-pie-collective.c")));
	}

	@Test
	public void mpi_pthreads_infinity_norm() throws ABCException {
		assertTrue(ui
				.run("verify",
						"-input_NPROCS=2 -inputNUM_ROWS_BOUND=2 -inputNUM_COLS_BOUND=2",
						"-enablePrintf=false",
						filename("mpi-pthreads-infinity-norm.c")));
	}

	@Test
	public void mpi_pthreads_matrix_vector() throws ABCException {
		assertFalse(ui
				.run("verify",
						"-input_NPROCS=2 -inputNUM_ROWS_BOUND=3",
						"-inputNUM_COLS_BOUND=3",
						"-showProgram=false -enablePrintf=false -showTransitions=false",
						filename("mpi-pthreads-marix-vector.c")));
		assertTrue(ui
				.run("verify",
						"-input_NPROCS=2 -inputNUM_ROWS_BOUND=3",
						"-inputNUM_COLS_BOUND=3",
						"-showProgram=false -enablePrintf=false -showTransitions=false",
						filename("mpi-pthreads-marix-vector_fix.c")));
	}

	@Test
	public void mpi_pthreads() throws ABCException {
		assertFalse(ui.run("verify", "-input_NPROCS=2 -showTransitions=false",
				"-showProgram=false -enablePrintf=false",
				filename("mpi-pthreads.c")));
	}

	@Test
	public void helloWorld() throws ABCException {
		assertTrue(ui.run("verify",
				"-input_NPROCS=2 -showModel=false -enablePrintf=false",
				"-showSavedStates=false",
				"-showTransitions=false -showProgram=false",
				"-showAmpleSet=false", filename("helloWorld.c")));
	}

	@Test
	public void hybrid() throws ABCException {
		assertFalse(ui.run("verify -input_NPROCS=2 -enablePrintf=false -min",
				filename("anl_hybrid.c")));
		assertFalse(ui.run("replay -showTransitions=false -enablePrintf=true",
				filename("anl_hybrid.c")));

	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
