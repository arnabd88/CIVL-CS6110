package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class IOTransformerTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "io");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void io() {
		assertTrue(ui.run("verify", filename("io.cvl"), "-enablePrintf=false"));
	}

	@Test
	public void scanf() {
		assertTrue(ui.run("verify", filename("fscanf.cvl")));
	}

	@Test
	public void defaultLength() {
		assertTrue(ui.run("verify", filename("defaultLength.cvl")));
	}
}
