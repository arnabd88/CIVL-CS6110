package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CompareBigTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "compare");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void diffusion1d() {
		assertTrue(ui.run("compare",
				"-input_mpi_nprocs_lo=1", "-input_mpi_nprocs_hi=3",
				"-inputNXB=8", "-inputNSTEPS_BOUND=4", "-spec",
				filename("diffusion1d/diffusion1d_spec.c"), "-impl",
				filename("diffusion1d/diffusion1d_par.c")));
	}
	
	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
