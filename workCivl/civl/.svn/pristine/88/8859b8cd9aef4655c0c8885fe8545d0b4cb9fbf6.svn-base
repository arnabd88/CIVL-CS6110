package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.UserInterface;

public class MessagePassingTest {

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"),
			"messagePassing");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Test
	public void ring() {
		assertTrue(ui.run("verify", filename("ring.cvl"), "-inputNPROCS=3"));
	}

}