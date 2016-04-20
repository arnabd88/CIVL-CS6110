package edu.udel.cis.vsl.civl;


import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class QuantifierTest {
	private static File rootDir = new File(new File("examples"), "experimental");
	
	private static UserInterface ui = new UserInterface();
	
	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}
	
	@Test
	public void quantifier() {
		assertTrue(ui.run("verify", "-showAmpleSet", filename("quantifier.c")));
	}
}
