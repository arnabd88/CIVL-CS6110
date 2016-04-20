package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPITranslationTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "mpi");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void ring1() {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=2", TestConstants.QUIET,
				filename("ring1.c")));
	}

	@Test
	public void ring1NotSaveStates() {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=2 -saveStates=false",
				TestConstants.QUIET, filename("ring1.c")));
	}

	@Test
	public void reduce() {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=4", TestConstants.QUIET,
				TestConstants.NO_PRINTF, filename("routines/reduce.c")));
	}

	@Test
	public void mpithreads_mpi() {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=2",
				"-enablePrintf=false", TestConstants.QUIET,
				filename("../mpi-pthread/mpithreads_mpi.c")));
	}

	@Test
	public void adder_par() {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=2", "-inputNB=4",
				TestConstants.QUIET, TestConstants.NO_PRINTF,
				filename("adder_par.c")));
	}

	@Test
	public void adder_comp() {
		assertTrue(ui.run("compare", "-enablePrintf=false",
				"-input_mpi_nprocs=2", "-inputNB=4", "-spec",
				TestConstants.QUIET, filename("seq/adder_spec.c"), "-impl",
				filename("adder_par.c")));
	}

	@Test
	public void mpi_scatter() throws ABCException {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=4",
				"-enablePrintf=false", TestConstants.QUIET,
				filename("routines/Gather_Scatter/mpi_scatter.c")));
	}

	@Test
	public void mpi_gather() throws ABCException {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=4",
				"-enablePrintf=false", TestConstants.QUIET,
				filename("routines/Gather_Scatter/mpi_gather.c")));
	}

	@Test
	public void mpi_gatherv() throws ABCException {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=4",
				"-enablePrintf=false", TestConstants.QUIET,
				filename("routines/Gather_Scatter/mpi_gather_inPlace.c")));
	}

	@Test
	public void mpi_scatterv() throws ABCException {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=4",
				"-enablePrintf=false", TestConstants.QUIET,
				filename("routines/Gather_Scatter/mpi_scatter_inPlace.c")));
	}

	@Test
	public void mpi_wave1d() throws ABCException {
		assertTrue(ui.run("verify", "-input_mpi_nprocs_hi=3",
				"-inputNSTEPSB=2", "-inputNXB=4", "-enablePrintf=false",
				TestConstants.QUIET, filename("wave1d.c")));
	}

	@Test
	public void mpi_diff2d() throws ABCException {
		assertTrue(ui.run("verify", "-input_mpi_nprocs=4", "-inputnsteps=2",
				"-inputnx=2", "-inputny=2", "-enablePrintf=false",
				"-inputNPROCSX=2", "-inputNPROCSY=2", TestConstants.QUIET,
				filename("diffusion2d.c")));
	}

	@Test
	public void mpi_diff2d1() throws ABCException {
		assertTrue(ui
				.run("verify -showTransitions=false -inputNSTEPSB=2 -inputNXB=1 -inputNYB=2 "
						+ "-inputNPROCSX=1 -inputNPROCSY=2 -enablePrintf=false",
						TestConstants.QUIET, filename("diffusion2d.c")));
	}

	@Test
	public void mpi_diff2dBad() throws ABCException {
		assertFalse(ui.run("verify", "-input_mpi_nprocs=4",
				"-enablePrintf=false", "-inputNPROCSX=2", "-inputNPROCSY=2",
				TestConstants.QUIET, filename("diffusion2dBad.c")));
	}

	@Test
	public void mpiSysStatus() {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				"-input_mpi_nprocs=3", TestConstants.QUIET,
				filename("routines/mpiSysStatus.c")));
	}

	@Test
	public void mpiSysStatusBad() {
		assertFalse(ui.run("verify", "-enablePrintf=false -input_mpi_nprocs=3",
				TestConstants.QUIET, filename("routines/mpiSysStatusBad.c")));
	}

	@Test
	public void mpiSysStatusBad2() {
		assertFalse(ui.run("verify", "-enablePrintf=false -input_mpi_nprocs=3",
				TestConstants.QUIET, filename("routines/mpiSysStatusBad2.c")));
	}

	@Test
	public void mpiPrime() {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				"-input_mpi_nprocs_hi=2", "-inputLIMITB=13",
				TestConstants.QUIET, filename("mpi_prime.c")));
	}

	@Test
	public void mpiMatmat() {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				"-input_mpi_nprocs_hi=3", "-inputNB=2", "-inputLB=2",
				"-inputMB=2", TestConstants.QUIET,
				filename("matmat_mw/matmat_mw.c")));
	}

	@Test
	public void mpiSumArray() {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				"-input_mpi_nprocs_hi=3", "-inputNB=8", TestConstants.QUIET,
				filename("sum_array.c")));
	}

	@Test
	public void sendrecv() {
		assertTrue(ui.run("verify -input_mpi_nprocs=3", TestConstants.QUIET,
				filename("sendrecv.c")));
	}

	@Test
	public void gaussJordan() {
		assertTrue(ui
				.run("verify -enablePrintf=false -inputnumRow=2 -inputnumCol=2 -input_mpi_nprocs=2",
						TestConstants.QUIET,
						filename("gaussJordan_elimination.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
