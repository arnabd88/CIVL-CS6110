package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.UserInterface;

public class AccuracyTest {

	/***************************** Static Fields *****************************/

	private static File rootDir = new File(new File("examples"), "accuracy");

	private static UserInterface ui = new UserInterface();

	/***************************** Helper Methods ****************************/

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/****************************** Test Methods *****************************/

	@Test
	public void derivative() {
		assertTrue(ui.run("verify", "-inputnum_elements=5",
				filename("derivative.cvl")));
	}

	@Test
	public void derivativeBad() {
		assertFalse(ui.run("verify", "-inputnum_elements=5",
				filename("derivativeBad.cvl")));
	}

	@Test
	public void secondDerivative() {
		assertTrue(ui.run("verify", "-inputnum_elements=5",
				filename("secondDerivative.cvl")));
	}

	@Test
	public void secondDerivativeBad() {
		assertTrue(ui.run("verify", "-inputnum_elements=5",
				filename("secondDerivativeBad.cvl")));
	}
	
	@Test
	public void diffusion() {
		assertTrue(ui.run("verify", "-inputn=4",
				filename("diffusion.cvl")));
	}

}
