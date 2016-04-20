package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

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
		assertTrue(ui.run("verify", filename("ring1.c"), "-input__NPROCS=5"));
	}

	@Test
	public void reduce() {
		assertTrue(ui.run("verify", filename("reduce.c"), "-input__NPROCS=2"));
	}

	@Test
	public void mpithreads_mpi() {
		assertTrue(ui.run("verify", filename("mpithreads_mpi.c"),
				"-input__NPROCS=2"));
	}

	@Test
	public void adder_par() {
		assertTrue(ui.run("verify", filename("adder_par.c"),
				"-input__NPROCS=2", "-inputNB=4"));
	}

	@Test
	public void mpi_pi_send() {
		assertTrue(ui.run("verify", filename("mpi_pi_send.c"),
				"-input__NPROCS=3", "-enablePrintf=false"));
	}

	@Test
	public void mpi_prime() {
		assertTrue(ui.run("verify", filename("mpi_prime.c"),
				"-input__NPROCS=4", "-enablePrintf=false"));
	}
}
