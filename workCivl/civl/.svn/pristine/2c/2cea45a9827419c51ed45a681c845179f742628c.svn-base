package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import org.junit.Test;

import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class ExamplesTest {

	private static File rootDir = new File("examples");
	private PrintStream out = System.out;

	@Test
	public void testAdder() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "adder.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testArrays() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "arrays.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testChoose() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "choose.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testDiffusion() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "diffusion_seq.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testLocks() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "locks.cvl");
		boolean result = CIVL.check(file, out);
		assertTrue(result);
	}

	@Test
	public void testMatmat() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "matmat.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testMinimal() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "minimal.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testPointers() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "pointers.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testSideEffects() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "sideEffects.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testSpawn() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "spawn.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testFor() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "for.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

	@Test
	public void testCompare() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "compare.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}
	
	@Test
	public void testEmptyBlock() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "emptyWhen.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}
	
	@Test
	public void testCast() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File file = new File(rootDir, "cast.cvl");
		boolean result = CIVL.check(file, out);
		assertFalse(result);
	}

}