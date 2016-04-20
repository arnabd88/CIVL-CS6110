package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import org.junit.Test;

import edu.udel.cis.vsl.abc.ABCException;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class LanguageFeaturesTest {

	private static File rootDir = new File("examples/languageFeatures");
	private PrintStream out = System.out;

	@Test
	public void testMalloc() throws ABCException {
		File file = new File(rootDir, "malloc.cvl");
		boolean result = CIVL.verify(true, false, file, out);
		assertTrue(result);
	}

	@Test
	public void testMallocBad() throws ABCException {
		File file = new File(rootDir, "mallocBad.cvl");
		boolean result = CIVL.verify(true, false, file, out);
		assertFalse(result);
	}

	@Test
	public void testMallocBad2() throws ABCException {
		File file = new File(rootDir, "mallocBad2.cvl");
		boolean result = CIVL.verify(true, false, file, out);
		assertFalse(result);
	}

	@Test
	public void testMallocBad3() throws ABCException {
		File file = new File(rootDir, "mallocBad3.cvl");
		boolean result = CIVL.verify(true, false, file, out);
		assertFalse(result);
	}

	@Test
	public void testMallocBad4() throws ABCException {
		File file = new File(rootDir, "mallocBad4.cvl");
		boolean result = CIVL.verify(true, false, file, out);
		assertFalse(result);
	}

	@Test
	public void testAssume() throws ABCException {
		File file = new File(rootDir, "assume.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testArrays() throws ABCException {
		File file = new File(rootDir, "arrays.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testBundleConcrete() throws ABCException {
		File file = new File(rootDir, "bundleConcrete.cvl");

		boolean result = CIVL.verify(true, false, file, out);
		assertTrue(result);
	}

	@Test
	public void testBundleArray() throws ABCException {
		File file = new File(rootDir, "bundleArray.cvl");

		boolean result = CIVL.verify(true, false, file, out);
		assertTrue(result);
	}

	@Test
	public void testBundleStruct() throws ABCException {
		File file = new File(rootDir, "bundleStruct.cvl");

		boolean result = CIVL.verify(true, false, file, out);
		assertTrue(result);
	}

	@Test
	public void testBundleStructComponent() throws ABCException {
		File file = new File(rootDir, "bundleStructComponent.cvl");

		boolean result = CIVL.verify(true, false, file, out);
		assertFalse(result);
	}

	@Test
	public void testBundleSize() throws ABCException {
		File file = new File(rootDir, "bundleSize.cvl");

		boolean result = CIVL.verify(true, false, file, out);
		assertTrue(result);
	}

	@Test
	public void testChoose() throws ABCException {
		File file = new File(rootDir, "choose.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testMinimal() throws ABCException {
		File file = new File(rootDir, "minimal.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testPointers() throws ABCException {
		File file = new File(rootDir, "pointers.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testLinkedList() throws ABCException {
		File file = new File(rootDir, "linkedList.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testSideEffects() throws ABCException {
		File file = new File(rootDir, "sideEffects.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testFor() throws ABCException {
		File file = new File(rootDir, "for.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testCompare() throws ABCException {
		File file = new File(rootDir, "compare.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testEmptyBlock() throws ABCException {
		File file = new File(rootDir, "emptyWhen.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testCast() throws ABCException {
		File file = new File(rootDir, "cast.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testSelf() throws ABCException {
		File file = new File(rootDir, "self.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testNonbooleanCondition() throws IOException,
			PreprocessorException, ParseException, SyntaxException {
		File file = new File(rootDir, "nonbooleanCondition.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testStruct() throws ABCException {
		File file = new File(rootDir, "struct.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testArrayPointer() throws ABCException {
		File file = new File(rootDir, "arrayPointer.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testScoping() throws ABCException {
		File file = new File(rootDir, "scoping.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testStructArray() throws ABCException {
		File file = new File(rootDir, "structArray.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testStructStruct() throws ABCException {
		File file = new File(rootDir, "structStruct.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testDynamicStruct() throws ABCException {
		File file = new File(rootDir, "dynamicStruct.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testSizeOf() throws ABCException {
		File file = new File(rootDir, "sizeOf.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testDuffs() throws ABCException {
		File file = new File(rootDir, "duffs.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}
	
	@Test
	public void testComm() throws ABCException {
		File file = new File(rootDir, "comm.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}

	@Test
	public void testBreak() throws ABCException {
		File file = new File(rootDir, "break.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}
	
	@Test
	public void testContinue() throws ABCException {
		File file = new File(rootDir, "continue.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}
	
	@Test
	public void testSwitch() throws ABCException {
		File file = new File(rootDir, "switch.cvl");
		boolean result = CIVL.verify(file, out);
		assertTrue(result);
	}
}