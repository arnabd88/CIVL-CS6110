package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;

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

	// TODO: why specify concrete values for K?
	@Ignore
	public void diffusion1d() {
		assertTrue(ui.run("compare", "-enablePrintf=false",
				"-input__NPROCS_LOWER_BOUND=1", "-input__NPROCS_UPPER_BOUND=1",
				"-inputNX=5", "-inputNSTEPSB=4", "-inputWSTEP=1",
				"-inputK=0.3", "-spec",
				filename("diffusion1d/diffusion1d_spec_revision.c"), "-impl",
				filename("diffusion1d/diffusion1d_par_revision.c")));
	}
}
