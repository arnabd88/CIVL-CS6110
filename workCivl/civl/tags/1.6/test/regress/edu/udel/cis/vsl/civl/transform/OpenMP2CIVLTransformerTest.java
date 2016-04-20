package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
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

	@Test
	public void dotProduct1() {
		assertTrue(ui.run("verify ", "-ompNoSimplify",
				"-input_omp_thread_max=2", filename("dotProduct1.c")));
	}

	@Test
	public void dotProduct1Simplify() {
		assertTrue(ui.run("verify ", "-input_omp_thread_max=2",
				filename("dotProduct1.c")));
	}

	@Test
	public void dotProductCritical() {
		assertTrue(ui.run("verify ", "-ompNoSimplify",
				"-input_omp_thread_max=2", filename("dotProduct_critical.c")));
	}

	@Test
	public void dotProductCriticalSimplify() {
		assertTrue(ui.run("verify ", "-input_omp_thread_max=2",
				filename("dotProduct_critical.c")));
	}

	@Test
	public void matProduct1Simplify() {
		assertTrue(ui.run("verify", "-input_omp_thread_max=2",
				filename("matProduct1.c")));
	}

	@Test
	public void parallelfor() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-input_omp_thread_max=2", filename("parallelfor.c")));
	}

	@Test
	public void parallelforSimplify() {
		assertTrue(ui.run("verify", "-input_omp_thread_max=2",
				filename("parallelfor.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
