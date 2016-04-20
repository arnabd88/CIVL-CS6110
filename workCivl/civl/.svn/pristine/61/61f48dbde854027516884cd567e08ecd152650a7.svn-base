package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class LibraryTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "library");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void string() throws ABCException {
		assertTrue(ui.run("verify", filename("string.cvl")));
	}

	@Test
	public void assertH() throws ABCException {
		assertTrue(ui.run("verify", filename("assert.cvl")));
	}

	@Test
	public void printf() throws ABCException {
		assertTrue(ui.run("verify", filename("stdio/printf.cvl")));
	}

	@Test
	public void printfBad() throws ABCException {
		assertFalse(ui.run("verify", filename("stdio/printfBad.cvl")));
	}

	@Test
	public void communicatorFeatures() {
		assertTrue(ui.run("verify", filename("civlc/communicatorFeatures.cvl"),
				"-inputNPROCS_BOUND=5", "-inputN_BOUND=3",
				"-enablePrintf=false"));
	}

	@Test
	public void commBad() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/commBad.cvl")));
	}

	@Test
	public void assertNonNullPointer() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/assertNonNullPointer.cvl")));
	}

	@Test
	public void assertNullPointer() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/assertNullPointer.cvl")));
	}

	@Test
	public void assertPrintf() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/assertPrintf.cvl")));
	}

	@Test
	public void memcpy() throws ABCException {
		assertTrue(ui.run("verify", filename("memcpy.cvl")));
	}

	@Test
	public void messageUnpackBad1() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/messageUnpackBad1.cvl")));
	}

	@Test
	public void messageUnpackBad2() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/messageUnpackBad2.cvl")));
	}

	@Test
	public void barrier() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/barrier.cvl"), "-inputB=5"));
	}

	@Test
	public void chooseInt() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/chooseInt.cvl")));
	}

	@Test
	public void exit() {
		assertTrue(ui.run("verify", filename("civlc/exit.cvl")));
	}

	@Test
	public void exitBad() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/exitBad.cvl")));
	}

	@Test
	public void intIter() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/intIter.cvl"), "-inputB=5"));
	}

	@Test
	public void contains() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/contains.cvl")));
	}

	@Test
	public void equals() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/equals.cvl")));
	}

	@Test
	public void translatePointer() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/translate_ptr.cvl")));
	}

	@Test
	public void copy() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/copy.cvl")));
	}

	@Test
	public void seqInit() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/seq_init.cvl")));
	}

	@Test
	public void freeBad1() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/freeBad1.cvl")));
	}

	@Test
	public void freeBad2() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/freeBad2.cvl")));
	}
}
