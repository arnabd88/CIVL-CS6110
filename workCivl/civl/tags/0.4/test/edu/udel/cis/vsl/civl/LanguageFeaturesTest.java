package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import edu.udel.cis.vsl.abc.ABCException;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.run.UserInterface;

public class LanguageFeaturesTest {

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"),
			"languageFeatures");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Test
	public void testMalloc() throws ABCException {
		assertTrue(ui.run("verify", filename("malloc.cvl")));
	}

	@Test
	public void testMallocBad() throws ABCException {
		assertFalse(ui.run("verify", filename("mallocBad.cvl")));
	}

	@Test
	public void testMallocBad2() throws ABCException {
		assertFalse(ui.run("verify", filename("mallocBad2.cvl")));
	}

	@Test
	public void testMallocBad3() throws ABCException {
		assertFalse(ui.run("verify", filename("mallocBad3.cvl")));
	}

	@Test
	public void testMallocBad4() throws ABCException {
		assertFalse(ui.run("verify", filename("mallocBad4.cvl")));
	}

	@Test
	public void testAssume() throws ABCException {
		assertTrue(ui.run("verify", filename("assume.cvl")));
	}

	@Test
	public void testArrays() throws ABCException {
		assertTrue(ui.run("verify", filename("arrays.cvl")));
	}

	@Test
	public void testBundleConcrete() throws ABCException {
		assertTrue(ui.run("verify", filename("bundleConcrete.cvl")));
	}

	@Test
	public void testBundleArray() throws ABCException {
		assertTrue(ui.run("verify", filename("bundleArray.cvl")));
	}

	@Test
	public void testBundleStruct() throws ABCException {
		assertTrue(ui.run("verify", filename("bundleStruct.cvl")));
	}

	@Test
	public void testBundleStructComponent() throws ABCException {
		assertFalse(ui.run("verify", filename("bundleStructComponent.cvl")));
	}

	@Test
	public void testBundleSize() throws ABCException {
		assertTrue(ui.run("verify", filename("bundleSize.cvl")));
	}

	@Test
	public void testChoose() throws ABCException {
		assertTrue(ui.run("verify", filename("choose.cvl")));
	}

	@Test
	public void testMinimal() throws ABCException {
		assertTrue(ui.run("verify", filename("minimal.cvl")));
	}

	@Test
	public void testPointers() throws ABCException {
		assertTrue(ui.run("verify", filename("pointers.cvl")));
	}

	@Test
	public void testLinkedList() throws ABCException {
		assertTrue(ui.run("verify", filename("linkedList.cvl")));
	}

	@Test
	public void testSideEffects() throws ABCException {
		assertTrue(ui.run("verify", filename("sideEffects.cvl")));
	}

	@Test
	public void testFor() throws ABCException {
		assertTrue(ui.run("verify", filename("for.cvl")));
	}

	@Test
	public void testCompare() throws ABCException {
		assertTrue(ui.run("verify", filename("compare.cvl")));
	}

	@Test
	public void testEmptyBlock() throws ABCException {
		assertTrue(ui.run("verify", filename("emptyWhen.cvl")));
	}

	@Test
	public void testCast() throws ABCException {
		assertTrue(ui.run("verify", filename("cast.cvl")));
	}

	@Test
	public void testSelf() throws ABCException {
		assertTrue(ui.run("verify", filename("self.cvl")));
	}

	@Test
	public void testNonbooleanCondition() throws IOException,
			PreprocessorException, ParseException, SyntaxException {
		assertTrue(ui.run("verify", filename("nonbooleanCondition.cvl")));
	}

	@Test
	public void testStruct() throws ABCException {
		assertTrue(ui.run("verify", filename("struct.cvl")));
	}

	@Test
	public void testArrayPointer() throws ABCException {
		assertTrue(ui.run("verify", filename("arrayPointer.cvl")));
	}

	@Test
	public void testScoping() throws ABCException {
		assertTrue(ui.run("verify", filename("scoping.cvl")));
	}

	@Test
	public void testStructArray() throws ABCException {
		assertTrue(ui.run("verify", filename("structArray.cvl")));
	}

	@Test
	public void testStructStruct() throws ABCException {
		assertTrue(ui.run("verify", filename("structStruct.cvl")));
	}

	@Test
	public void testDynamicStruct() throws ABCException {
		assertTrue(ui.run("verify", filename("dynamicStruct.cvl")));
	}

	@Test
	public void testSizeOf() throws ABCException {
		assertTrue(ui.run("verify", filename("sizeOf.cvl")));
	}

	@Test
	public void testDuffs() throws ABCException {
		assertTrue(ui.run("verify", filename("duffs.cvl")));
	}

	@Test
	public void testComm() throws ABCException {
		assertTrue(ui.run("verify", filename("comm.cvl")));
	}

	@Test
	public void testBreak() throws ABCException {
		assertTrue(ui.run("verify", filename("break.cvl")));
	}

	@Test
	public void testContinue() throws ABCException {
		assertTrue(ui.run("verify", filename("continue.cvl")));
	}

	@Test
	public void testSwitch() throws ABCException {
		assertTrue(ui.run("verify", filename("switch.cvl")));
	}

	@Test
	public void testMemcpy() throws ABCException {
		assertTrue(ui.run("verify", filename("memcpy.cvl")));
	}
}