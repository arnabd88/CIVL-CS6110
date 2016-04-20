package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
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
		assertTrue(ui.run("verify", "-enablePrintf=false", TestConstants.QUIET, filename("io.cvl")));
	}

	@Test
	public void scanf() {
		assertTrue(ui.run("verify", TestConstants.QUIET, filename("fscanf.cvl")));
	}

	@Test
	public void stringTestBad() {
		try {
			assertFalse(ui.run("verify -DNEGINDEX", TestConstants.QUIET, filename("fileOpen.cvl")));
		} catch (CIVLInternalException e) {
			System.out.println(e.getMessage());
		}
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("fileOpen.cvl")));
		assertFalse(ui.run("verify -DNCINDEX", TestConstants.QUIET, filename("fileOpen.cvl")));
		assertFalse(ui.run("verify -DNCARRAY", TestConstants.QUIET, filename("fileOpen.cvl")));
		assertFalse(ui.run("verify -DSCHAR", TestConstants.QUIET, filename("fileOpen.cvl")));
	}

	@Test
	public void defaultLength() {
		assertTrue(ui.run("verify", TestConstants.QUIET, filename("defaultLength.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
