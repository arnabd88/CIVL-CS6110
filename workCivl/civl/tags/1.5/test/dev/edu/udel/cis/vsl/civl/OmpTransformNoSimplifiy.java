package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class OmpTransformNoSimplifiy {

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
		assertTrue(ui.run("verify", "-ompNoSimplify", "-input_omp_thread_max=4",
				filename("dotProduct1.c")));
	}

	@Test
	public void dotProductCritical() {
		assertTrue(ui.run("verify", "-ompNoSimplify", "-input_omp_thread_max=4",
				filename("dotProduct_critical.c")));
	}

	@Test
	public void matProduct1() {
		assertTrue(ui.run("verify", "-ompNoSimplify -showAmpleSetWtStates -enablePrintf=false",
				"-input_omp_thread_max=2", filename("matProduct1.c")));
	}

	@Test
	public void parallelfor() {
		assertTrue(ui.run("verify", "-ompNoSimplify", "-input_omp_thread_max=4",
				filename("parallelfor.c")));
	}

	@Test
	public void raceCond1() {
		assertTrue(ui.run("verify", "-showTransitions -ompNoSimplify",
				"-input_omp_thread_max=4", filename("raceCond1.c")));
	}

	@Test
	public void raceCond2() {
		assertTrue(ui.run("verify", "-showProgram -ompNoSimplify",
				"-input_omp_thread_max=4", filename("raceCond2.c")));
	}

	@Test
	public void canonicalForLoops() {
		assertTrue(ui.run("verify", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("canonicalForLoops.c")));
	}

}
