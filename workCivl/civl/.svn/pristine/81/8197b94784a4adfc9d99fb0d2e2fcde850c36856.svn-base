package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.PrintStream;

import org.junit.Test;

import edu.udel.cis.vsl.abc.ABCException;

public class ConcurrencyTest {

	private static File rootDir = new File("examples/concurrency");
	private PrintStream out = System.out;

	@Test
	public void testAdder() throws ABCException {
		File file = new File(rootDir, "adder.cvl");
		boolean result = CIVL.verify(true, false, file, out);
		assertTrue(result);
	}

	@Test
	public void testLocks() throws ABCException {
		File file = new File(rootDir, "locks.cvl");
		boolean result = CIVL.verify(file, out);
		assertFalse(result);
	}

	@Test
	public void testSpawn() throws ABCException {
		File file = new File(rootDir, "spawn.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testBarrier() throws ABCException {
		File file = new File(rootDir, "barrier.cvl");
		boolean result = CIVL.verify(true, false, file, out);
		assertTrue(result);
	}

	@Test
	public void testBarrier2() throws ABCException {
		File file = new File(rootDir, "barrier2.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testDining() throws ABCException {
		File file = new File(rootDir, "dining.cvl");
		boolean result = CIVL.verify(file, out);
		assertFalse(result);
	}

}