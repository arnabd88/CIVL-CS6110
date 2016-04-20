package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPITranslationBigTest {

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
	public void mpi_prime() {
		assertTrue(ui.run("verify",
				"-input__NPROCS=4", "-enablePrintf=false", filename("mpi_prime.c")));
	}

}
