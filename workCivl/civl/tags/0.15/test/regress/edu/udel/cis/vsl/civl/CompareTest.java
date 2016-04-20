package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CompareTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "compare");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void sumN() {
		assertTrue(ui.run("compare", "-inputN=10", "-spec",
				filename("sumNspec.cvl"), "-impl", filename("sumNimpl.cvl")));
	}

	@Test
	public void adder() {
		assertTrue(ui.run("compare", "-enablePrintf=false", "-inputNPROCSB=2",
				"-inputNB=4", "-spec", filename("adder/adder_par.cvl"),
				"-impl", filename("adder/adder_spec.cvl")));
	}

	@Test
	public void max() {
		assertFalse(ui.run("compare -inputB=4 -min -spec",
				filename("max/max.cvl"), filename("max/max_seq.cvl"),
				"-impl -inputNPROCS=2 -inputBLOCK_SIZE=2",
				filename("max/max.cvl"), filename("max/max_par.cvl")));
		assertFalse(ui.run("replay -inputB=4 -min -spec",
				filename("max/max.cvl"), filename("max/max_seq.cvl"),
				"-impl -inputNPROCS=2 -inputBLOCK_SIZE=2",
				filename("max/max.cvl"), filename("max/max_par.cvl")));
	}

}
