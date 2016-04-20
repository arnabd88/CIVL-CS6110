package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class OmpOrphanTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dotProductOrphan() {
		assertTrue(ui.run("verify", "-ompNoSimplify", "-inputTHREAD_MAX=4",
				filename("dotProduct_orphan.c")));
	}
	
	@Test
	public void piOrphan() {
		assertTrue(ui.run("verify", "-ompNoSimplify", "-inputTHREAD_MAX=4",
				filename("pi_orphan.c")));
	}

	

}
