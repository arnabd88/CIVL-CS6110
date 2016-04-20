package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.PrintStream;

import org.junit.Test;

import edu.udel.cis.vsl.abc.ABCException;

public class ArithmeticTest {

	private static File rootDir = new File("examples/arithmetic");
	private PrintStream out = System.out;

	@Test
	public void testDiffusion() throws ABCException {
		File file = new File(rootDir, "diffusion_seq.cvl");
		boolean result = CIVL.verify(true, false, file, out);
		assertTrue(result);
	}

	@Test
	public void testMatmat() throws ABCException {
		File file = new File(rootDir, "matmat.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}
	
	@Test
	public void testLaplace() throws ABCException {
		File file = new File(rootDir, "laplace.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}
	
	@Test
	public void testAssoc() throws ABCException {
		File file = new File(rootDir, "assoc.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}
	
	@Test
	public void testAlgebra() throws ABCException {
		File file = new File(rootDir, "algebra.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}
	
	@Test
	public void testDerivative() throws ABCException {
		File file = new File(rootDir, "derivative.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testDivision() throws ABCException {
		File file = new File(rootDir, "division.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}
}