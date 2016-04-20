package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPITranslationBigTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"mpi");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void mpi_prime() {
		assertTrue(ui.run("verify", "-input_NPROCS=4", "-enablePrintf=false",
				filename("mpi_prime.c")));
	}

	@Test
	public void mpi_wave1d() {
		assertTrue(ui
				.run("verify", "-enablePrintf=false", filename("wave1d.c")));
	}

	@Test
	public void mpi_diff1d() {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				filename("diffusion1d.c")));
	}

	@Test
	public void mpi_diff2d() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-input_NPROCS=4",
				"-inputNPROCSX=2", "-inputNPROCSY=2", "-inputNSTEPSB=3",
				filename("diffusion2d.c")));
	}

	@Test
	public void mpi_pi() {
		assertTrue(ui
				.run("verify", "-enablePrintf=false", filename("mpi_pi.c")));
	}

}
