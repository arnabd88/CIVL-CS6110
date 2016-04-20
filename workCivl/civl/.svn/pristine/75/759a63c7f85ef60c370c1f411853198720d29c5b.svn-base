package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPITranslationTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"translation/mpi");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void ring1() {
		assertTrue(ui.run("verify", "-input__NPROCS=2", filename("ring1.c")));
	}

	@Test
	public void reduce() {
		assertTrue(ui.run("verify", "-input__NPROCS=2",
				"-enablePrintf=false", filename("reduce.c")));
	}

	@Test
	public void mpithreads_mpi() {
		assertTrue(ui.run("verify",
				"-input__NPROCS=2", "-enablePrintf=false", filename("mpithreads_mpi.c")));
	}

	@Test
	public void adder_par() {
		assertTrue(ui.run("verify",
				"-input__NPROCS=2", "-inputNB=4", "-enablePrintf=false", filename("adder_par.c")));
	}

	@Test
	public void adder_comp() {
		assertTrue(ui.run("compare", "-enablePrintf=false", "-input__NPROCS=2",
				"-inputNB=4", "-spec", filename("seq/adder_spec.c"), "-impl",
				filename("adder_par.c")));
	}

	@Ignore
	@Test
	public void mpi_pi_send() {
		assertTrue(ui.run("verify",
				"-input__NPROCS=3", "-enablePrintf=false", filename("mpi_pi_send.c")));
	}

	@Ignore
	@Test
	public void pi_comp() {
		assertTrue(ui.run("compare", "-input__NPROCS=3",
				filename("seq/ser_pi_calc.c"), filename("mpi_pi_send.c")));
	}

	@Test
	public void mpi_scatter() throws ABCException {
		assertTrue(ui.run("verify",
				"-input__NPROCS=4", "-enablePrintf=false", filename("Gather_Scatter/mpi_scatter.c")));
	}

	@Test
	public void mpi_gather() throws ABCException {
		assertTrue(ui.run("verify",
				"-input__NPROCS=4", "-enablePrintf=false", filename("Gather_Scatter/mpi_gather.c")));
	}

	@Test
	public void mpi_gatherv() throws ABCException {
		assertTrue(ui.run("verify",
				"-input__NPROCS=4", "-enablePrintf=false",
				filename("Gather_Scatter/mpi_gather_inPlace.c")));
	}

	@Test
	public void mpi_scatterv() throws ABCException {
		assertTrue(ui.run("verify",
				"-input__NPROCS=4", "-enablePrintf=false",
				filename("Gather_Scatter/mpi_scatter_inPlace.c")));
	}
}
