package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.UserInterface;

public class MessagePassingTest {

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
	public void ring() {
		assertTrue(ui.run("verify", filename("ring.cvl"), "-inputNPROCS=3"));
	}

	@Test
	public void ring2() {
		assertTrue(ui.run("verify", filename("ring2.cvl"), "-inputNPROCS=3"));
	}

	@Test
	public void hybrid() {
		assertFalse(ui.run("verify", filename("hybrid.cvl")));
	}

	// takes too long (forever?)
	@Ignore
	@Test
	public void hybridMin() {
		assertFalse(ui.run("verify", "-min", filename("hybrid.cvl")));
	}

	@Test
	public void hybrid2() {
		assertFalse(ui.run("verify", filename("hybrid2.cvl"), "-inputNPROCS=2"));
	}

	// takes too long (forever?)
	@Ignore
	@Test
	public void hybrid2Min() {
		assertFalse(ui.run("verify", filename("hybrid2.cvl"), "-inputNPROCS=2",
				"-min"));
	}

}