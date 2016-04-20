package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class OpenMP2CIVLTransformerTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Ignore
	@Test
	public void dotProduct1() {
		assertTrue(ui.run("show -showModel", "-ompNoSimplify",
				"-inputTHREAD_MAX=4", filename("dotProduct1.c")));
	}

	@Ignore
	@Test
	public void dotProductCritical() {
		assertTrue(ui.run("show -showModel", "-ompNoSimplify",
				"-inputTHREAD_MAX=4", filename("dotProduct_critical.c")));
	}

	@Ignore
	@Test
	public void matProduct1() {
		assertTrue(ui.run("show -showModel", "-ompNoSimplify",
				"-inputTHREAD_MAX=4", filename("matProduct1.c")));
	}

	@Ignore
	@Test
	public void parallelfor() {
		assertTrue(ui.run("show -showModel", "-ompNoSimplify",
				"-inputTHREAD_MAX=4", filename("parallelfor.c")));
	}

	@Ignore
	@Test
	public void raceCond1() {
		assertTrue(ui.run("show -showModel", "-ompNoSimplify",
				"-inputTHREAD_MAX=4", filename("raceCond1.c")));
	}
	
	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
