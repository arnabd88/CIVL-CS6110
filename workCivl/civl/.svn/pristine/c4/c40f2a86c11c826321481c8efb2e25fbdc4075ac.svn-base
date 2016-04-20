package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class OpenMP2CIVLTransformerTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	
	@Ignore
	@Test
	public void dotProduct() {
		assertTrue(ui.run("parse", filename("dotProduct.c"), "-ompNoSimplify", "-inputTHREAD_MAX=4"));
	}
	
	@Ignore
	@Test
	public void dotProductCritical() {
		assertTrue(ui.run("parse", filename("dotProduct_critical.c"), "-ompNoSimplify", "-inputTHREAD_MAX=4"));
	}
	
	@Ignore
	@Test
	public void matProduct1() {
		assertTrue(ui.run("parse", filename("matProduct1.c"), "-ompNoSimplify", "-inputTHREAD_MAX=4"));
	}
	
	@Ignore
	@Test
	public void parallelfor() {
		assertTrue(ui.run("parse", filename("parallelfor.c"), "-ompNoSimplify", "-inputTHREAD_MAX=4"));
	}
	
	@Ignore
	@Test
	public void raceCond1() {
		assertTrue(ui.run("parse", filename("raceCond1.c"), "-ompNoSimplify", "-inputTHREAD_MAX=4"));
	}
}
