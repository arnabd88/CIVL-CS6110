package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MessagePassingBigTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"messagePassing");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void hybridMin() {
		assertFalse(ui
				.run("verify -inputNPROCS=2 -min", filename("hybrid.cvl")));
	}

	@Test
	public void diffusion1d() {
		assertTrue(ui.run("verify", "-inputNPROCSB=3", "-inputNSTEPSB=3",
				"-inputNXB=6", "-enablePrintf=false",
				filename("diffusion1d.cvl")));
	}

}