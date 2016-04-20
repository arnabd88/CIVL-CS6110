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
		assertTrue(ui.run("verify", "-enablePrintf=false",
				filename("stdio/printf.cvl")));
	}

	@Test
	public void printfBad() throws ABCException {
		assertFalse(ui.run("verify", filename("stdio/printfBad.cvl")));
	}

	@Test
	public void communicatorFeatures() {
		assertTrue(ui.run("verify", "-inputNPROCS_BOUND=2", "-inputN_BOUND=2",
				"-enablePrintf=false",
				filename("civlc/communicatorFeatures.cvl")));
	}

	@Test
	public void commBad() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/commBad.cvl")));
	}

	@Test
	public void malloc1() throws ABCException {
		assertTrue(ui.run("verify", filename("malloc.cvl")));
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
		assertTrue(ui.run("verify", "-inputB=5", filename("civlc/barrier.cvl")));
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
		assertTrue(ui.run("verify", "-inputB=5", "-enablePrintf=false",
				filename("civlc/intIter.cvl")));
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
	public void seq() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/seq.cvl")));
	}

	@Test
	public void freeBad1() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/freeBad1.cvl")));
	}

	@Test
	public void freeBad2() throws ABCException {
		assertFalse(ui.run("verify", filename("civlc/freeBad2.cvl")));
	}

	@Test
	public void bundleAndHeap() throws ABCException {
		assertTrue(ui.run("verify", filename("civlc/bundleAndHeap.cvl")));
	}

	@Test
	public void domainDecomp() throws ABCException {
		assertTrue(ui.run("verify", "-inputn=4", "-enablePrintf=false",
				filename("civlc/domainDecomposition.cvl")));
	}
}
