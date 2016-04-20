package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
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
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("dotProduct1.c")));
	}

	@Test
	public void dotProductCritical() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("dotProduct_critical.c")));
	}
	
	@Test
	public void dotProductOrphan() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("dotProduct_orphan.c")));
	}

	@Test
	public void matProduct1() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify",
				"-input_omp_thread_max=2", filename("matProduct1.c")));
	}

	@Test
	public void parallelfor() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("parallelfor.c")));
	}
	
	@Test
	public void sections() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("sections.c")));
	}
	
	@Test
	public void threadPrivate() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("threadPrivate.c")));
	}
	
	@Test
	public void lastPrivate() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("lastPrivate.c")));
	}
	
	@Test
	public void vecAdd() {
		assertFalse(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("vecAdd_deadlock.c")));
	}

	@Ignore
	@Test
	public void raceCond1() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify",
				"-input_omp_thread_max=2", filename("raceCond1.c")));
	}

	@Ignore
	@Test
	public void raceCond2() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-showProgram -ompNoSimplify",
				"-input_omp_thread_max=2", filename("raceCond2.c")));
	}

	@Test
	public void canonicalForLoops() {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-ompNoSimplify", "-input_omp_thread_max=2",
				filename("canonicalForLoops.c")));
	}

}
