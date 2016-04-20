package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ErrorStateEquivTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File("examples", "seq");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */


	@Test
	public void onepath_default() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", filename("onepath.c")));
	}

	@Test
	public void onepath_loc() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", "-errorStateEquiv=LOC", filename("onepath.c")));
	}
	
	@Test
	public void onepath_call() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", "-errorStateEquiv=CALLSTACK", filename("onepath.c")));
	}
	
	@Test
	public void onepath_full() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", "-errorStateEquiv=FULL", filename("onepath.c")));
	}
	
	@Test
	public void twopath_default() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", filename("twopath.c")));
	}

	@Test
	public void twopath_loc() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", "-errorStateEquiv=LOC", filename("twopath.c")));
	}
	
	@Test
	public void twopath_call() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", "-errorStateEquiv=CALLSTACK", filename("twopath.c")));
	}
	
	@Test
	public void twopath_full() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", "-errorStateEquiv=FULL", filename("twopath.c")));
	}
	
	@Test
	public void callpath_loc() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", "-errorStateEquiv=LOC", filename("callpath.c")));
	}
	
	@Test
	public void callpath_call() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", "-errorStateEquiv=CALLSTACK", filename("callpath.c")));
	}
	
	@Test
	public void callpath_full() throws ABCException {
		assertFalse(ui.run("verify", "-errorBound=5", "-errorStateEquiv=FULL", filename("callpath.c")));
	}
	
}
