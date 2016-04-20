package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class LibraryTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "library");

	private static UserInterface ui = new UserInterface();

	private final static String CIVLC = "civlc";

	// private final static String OMP = "omp";

	private final static String STDIO = "stdio";

	private final static String STDLIB = "stdlib";
	private final static String STRING = "string";
	private final static String TIME = "time";
	private final static String POINTER = "pointer";
	private final static String EXTERNAL = "external";
	private final static String MATH = "math";

	/* *************************** Helper Methods *************************** */

	private static String filename(String subfolder, String name) {
		return new File(new File(rootDir, subfolder), name).getPath();
	}

	private static String filename(String name) {
		return filename(".", name);
	}

	/* **************************** Test Methods *************************** */
	@Test
	public void assertBad() throws ABCException {
		assertFalse(ui.run("verify", filename(CIVLC, "assertBad.cvl")));
	}

	@Test
	public void elaborate() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "elaborate.cvl")));
	}

	@Test
	public void elaborate1() throws ABCException {
		assertTrue(ui
				.run("verify -showTransitions=false -showPathCondition=false -enablePrintf=false",
						filename(CIVLC, "elaborate1.cvl")));
	}

	@Test
	public void string() throws ABCException {
		assertTrue(ui.run("verify", filename(STRING, "string_test.cvl")));
	}

	@Test
	public void memset() throws ABCException {
		assertTrue(ui.run("verify", filename(STRING, "memset.cvl")));
	}

	@Test
	public void assertH() throws ABCException {
		assertTrue(ui.run("verify", filename("assert_test.cvl")));
	}

	@Test
	public void printf() throws ABCException {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				filename(STDIO, "printf.cvl")));
	}

	@Test
	public void printfBad() throws ABCException {
		assertFalse(ui.run("verify", filename(STDIO, "printfBad.cvl")));
	}

	@Test
	public void communicatorFeatures() {
		assertTrue(ui.run("verify", "-inputNPROCS=2", "-inputN_BOUND=2",
				"-enablePrintf=false",
				filename(CIVLC, "communicatorFeatures.cvl")));
	}

	@Test
	public void commBad() throws ABCException {
		assertFalse(ui.run("verify", filename(CIVLC, "commBad.cvl")));
	}

	@Test
	public void malloc1() throws ABCException {
		assertTrue(ui.run("verify", filename(STDLIB, "malloc.cvl")));
	}

	@Test
	public void mallocForSturct() throws ABCException {
		assertTrue(ui.run("verify", filename(STDLIB, "mallocForStruct.cvl")));

	}

	@Test
	public void memcpy() throws ABCException {
		assertTrue(ui.run("verify", filename(STRING, "memcpy.cvl")));
	}

	@Test
	public void messageUnpackBad1() throws ABCException {
		assertFalse(ui.run("verify", filename(CIVLC, "messageUnpackBad1.cvl")));
	}

	@Test
	public void messageUnpackBad2() throws ABCException {
		assertFalse(ui.run("verify", filename(CIVLC, "messageUnpackBad2.cvl")));
	}

	@Test
	public void barrier() throws ABCException {
		assertTrue(ui.run("verify", "-inputB=5 -showSavedStates",
				filename(CIVLC, "barrier.cvl")));
	}

	@Test
	public void chooseInt() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "chooseInt.cvl")));
	}

	@Test
	public void exit() {
		assertTrue(ui.run("verify", filename(CIVLC, "exit.cvl")));
	}

	@Test
	public void exitBad() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "exitBad.cvl")));
	}

	@Test
	public void intIter() throws ABCException {
		assertTrue(ui.run("verify", "-inputB=5", "-enablePrintf=false",
				filename(CIVLC, "intIter.cvl")));
	}

	@Test
	public void contains() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "contains.cvl")));
	}

	@Test
	public void equals() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "equals.cvl")));
	}

	@Test
	public void translatePointer() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "translate_ptr.cvl")));
	}

	@Test
	public void copy() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "copy.cvl")));
	}

	@Test
	public void seq() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "seq.cvl")));
	}

	@Test
	public void freeBad1() throws ABCException {
		assertFalse(ui.run("verify", filename(CIVLC, "freeBad1.cvl")));
	}

	@Test
	public void freeBad2() throws ABCException {
		assertFalse(ui.run("verify", filename(CIVLC, "freeBad2.cvl")));
	}

	@Test
	public void bundleAndHeap() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "bundleAndHeap.cvl")));
	}

	@Test
	public void random() throws ABCException {
		assertFalse(ui.run("verify", filename(STDLIB, "random.cvl")));
	}

	@Test
	public void rand_r() throws ABCException {
		assertTrue(ui.run("verify -D_LINUX", filename(STDLIB, "rand_r.c")));
	}

	@Test
	public void domainDecomp() throws ABCException {
		assertTrue(ui.run("verify", "-inputn=4",
				"-enablePrintf=false -showTransitions",
				filename(CIVLC, "domainDecomposition.cvl")));
	}

	@Test
	public void timeTest() throws ABCException {
		assertTrue(ui.run("verify", "-inputN=10",
				"-enablePrintf=false -showProgram=false",
				filename(TIME, "timeTest.cvl")));
	}

	@Test
	public void localTime() throws ABCException {
		assertTrue(ui.run("verify -enablePrintf=false",
				filename(TIME, "localTime.c")));
	}

	@Test
	public void assertEquals() throws ABCException {
		assertTrue(ui.run("verify -enablePrintf=false",
				filename(POINTER, "simpleAssertEquals.cvl")));
		assertTrue(ui.run("verify -enablePrintf=false",
				filename(POINTER, "simpleAssertEquals2.cvl")));
	}

	@Test
	public void assertEqualsFail() throws ABCException {
		assertFalse(ui.run("verify -enablePrintf=false",
				filename(POINTER, "simpleAssertEqualsFail.cvl")));
		assertFalse(ui.run("verify -enablePrintf=false",
				filename(POINTER, "simpleAssertEqualsFail2.cvl")));
	}

	@Test
	public void defined() throws ABCException {
		assertTrue(ui.run("verify -enablePrintf=false",
				filename(CIVLC, "defined.cvl")));
	}

	@Test
	public void assume() throws ABCException {
		assertTrue(ui.run("verify -showProgram", filename(CIVLC, "assume.cvl")));
	}

	@Test
	public void fprintfExit() throws ABCException {
		assertTrue(ui.run("verify", filename(STDIO, "fprintfExit.cvl")));
	}

	@Test
	public void scanfExit() throws ABCException {
		assertTrue(ui.run("verify", filename(STDIO, "scanfExit.cvl")));
	}

	@Test
	public void systemFunctionPointer() throws ABCException {
		assertTrue(ui.run("verify", filename("funcPointer.cvl")));
	}

	@Test
	public void pathcondition() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "pathcondition.cvl")));
	}

	@Test
	public void isConcreteInt() throws ABCException {
		assertTrue(ui.run("verify", filename(CIVLC, "concreteIntTest.cvl")));
	}

	@Test
	public void elaborateDomain() throws ABCException {
		assertTrue(ui.run("verify -enablePrintf=false",
				filename(CIVLC, "elaborateDomain.cvl")));
	}

	@Test
	public void testMyLib() throws ABCException {
		assertFalse(ui
				.run("verify -showTransitions=false -showStates=false -errorBound=100",
						filename(EXTERNAL, "testMyLib.cvl")));
	}

	@Test
	public void sqrt() throws ABCException {
		assertTrue(ui.run("verify ", filename(MATH, "sqrt.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
