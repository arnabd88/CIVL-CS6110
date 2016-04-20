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

	/***************************** Static Fields *****************************/

	private static File rootDir = new File(new File("examples"),
			"languageFeatures");

	private static UserInterface ui = new UserInterface();

	/***************************** Helper Methods *****************************/

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/****************************** Test Methods *****************************/

	@Test
	public void arrayPointer() throws ABCException {
		assertTrue(ui.run("verify", filename("arrayPointer.cvl")));
	}

	@Test
	public void arrays() throws ABCException {
		assertTrue(ui.run("verify", filename("arrays.cvl")));
	}

	@Test
	public void arrayLiteral() throws ABCException {
		assertTrue(ui.run("verify", filename("arrayLiteral.cvl")));
	}

	@Test
	public void assertNonNullPointer() throws ABCException {
		assertTrue(ui.run("verify", filename("assertNonNullPointer.cvl")));
	}

	@Test
	public void assertNullPointer() throws ABCException {
		assertFalse(ui.run("verify", filename("assertNullPointer.cvl")));
	}

	@Test
	public void assertPrintf() throws ABCException {
		assertFalse(ui.run("verify", filename("assertPrintf.cvl")));
	}

	@Test
	public void assume() throws ABCException {
		assertTrue(ui.run("verify", filename("assume.cvl")));
	}

	@Test
	public void atomChooseBad() throws ABCException {
		assertFalse(ui.run("verify", filename("atomChooseBad.cvl")));
	}

	@Test
	public void atomicBlockedResume() throws ABCException {
		assertTrue(ui.run("verify", filename("atomicBlockedResume.cvl")));
	}

	@Test
	public void atomicStatement() throws ABCException {
		assertTrue(ui.run("verify", filename("atomicStatement.cvl")));
	}

	@Test
	public void atomicWait() throws ABCException {
		assertTrue(ui.run("verify", "-inputN=3", filename("atomicWait.cvl")));
	}

	@Test
	public void atomStatement() throws ABCException {
		assertTrue(ui.run("verify", filename("atomStatement.cvl")));
	}

	@Test
	public void atomWaitBad() throws ABCException {
		assertFalse(ui.run("verify", filename("atomWaitBad.cvl")));
	}

	@Test
	public void bigO() {
		assertTrue(ui.run("verify", filename("bigO.cvl")));
	}

	@Test
	public void breakStatement() throws ABCException {
		assertTrue(ui.run("verify", filename("break.cvl")));
	}

	@Test
	public void bundleArray() throws ABCException {
		assertTrue(ui.run("verify", filename("bundleArray.cvl")));
	}

	@Test
	public void bundleConcrete() throws ABCException {
		assertTrue(ui.run("verify", filename("bundleConcrete.cvl")));
	}

	@Test
	public void bundleSize() throws ABCException {
		assertTrue(ui.run("verify", filename("bundleSize.cvl")));
	}

	@Test
	public void bundleStruct() throws ABCException {
		assertTrue(ui.run("verify", filename("bundleStruct.cvl")));
	}

	@Test
	public void bundleStructComponent() throws ABCException {
		assertFalse(ui.run("verify", filename("bundleStructComponent.cvl")));
	}

	@Test
	public void cAssert() throws ABCException {
		assertFalse(ui.run("verify", filename("cAssert.cvl")));
	}

	@Test
	public void cast() throws ABCException {
		assertTrue(ui.run("verify", filename("cast.cvl")));
	}

	@Test
	public void charTest() throws ABCException {
		assertTrue(ui.run("verify", filename("char.cvl")));
	}

	@Test
	public void choose() throws ABCException {
		assertTrue(ui.run("verify", filename("choose.cvl")));
	}

	@Test
	public void chooseInt() throws ABCException {
		assertTrue(ui.run("verify", filename("chooseInt.cvl")));
	}

	@Test
	public void commBad() throws ABCException {
		assertFalse(ui.run("verify", filename("commBad.cvl")));
	}

	@Test
	public void compare() throws ABCException {
		assertTrue(ui.run("verify", filename("compare.cvl")));
	}

	@Test
	public void conditionalExpression() throws ABCException {
		assertTrue(ui.run("verify", filename("conditionalExpression.cvl")));
	}

	@Test
	public void continueStatement() throws ABCException {
		assertTrue(ui.run("verify", filename("continue.cvl")));
	}

	@Test
	public void duffs() throws ABCException {
		assertTrue(ui.run("verify", filename("duffs.cvl")));
	}

	@Test
	public void dynamicStruct() throws ABCException {
		assertTrue(ui.run("verify", filename("dynamicStruct.cvl")));
	}

	@Test
	public void emptyWhen() throws ABCException {
		assertTrue(ui.run("verify", filename("emptyWhen.cvl")));
	}

	@Test
	public void exit() {
		assertTrue(ui.run("verify", filename("exit.cvl")));
	}

	@Test
	public void forLoop() throws ABCException {
		assertTrue(ui.run("verify", filename("for.cvl")));
	}

	@Test
	public void functionPrototype() throws ABCException {
		assertTrue(ui.run("verify", filename("functionPrototype.cvl")));
	}

	@Test
	public void implies() throws ABCException {
		assertTrue(ui.run("verify", filename("implies.cvl")));
	}

	@Test
	public void linkedList() throws ABCException {
		assertTrue(ui.run("verify", filename("linkedList.cvl")));
	}

	@Test
	public void malloc() throws ABCException {
		assertTrue(ui.run("verify", filename("malloc.cvl")));
	}

	@Test
	public void mallocBad() throws ABCException {
		assertFalse(ui.run("verify", filename("mallocBad.cvl")));
	}

	@Test
	public void mallocBad2() throws ABCException {
		assertFalse(ui.run("verify", filename("mallocBad2.cvl")));
	}

	@Test
	public void mallocBad3() throws ABCException {
		assertFalse(ui.run("verify", filename("mallocBad3.cvl")));
	}

	@Test
	public void mallocBad4() throws ABCException {
		assertFalse(ui.run("verify", filename("mallocBad4.cvl")));
	}

	@Test
	public void memcpy() throws ABCException {
		assertTrue(ui.run("verify", filename("memcpy.cvl")));
	}

	@Test
	public void minimal() throws ABCException {
		assertTrue(ui.run("verify", filename("minimal.cvl")));
	}

	@Test
	public void nonbooleanCondition() throws IOException,
			PreprocessorException, ParseException, SyntaxException {
		assertTrue(ui.run("verify", filename("nonbooleanCondition.cvl")));
	}

	@Test
	public void nullPointer() throws ABCException {
		assertTrue(ui.run("verify", filename("null.cvl")));
	}

	@Test
	public void pointers() throws ABCException {
		assertTrue(ui.run("verify", filename("pointers.cvl")));
	}

	@Test
	public void printf() throws ABCException {
		assertTrue(ui.run("verify", filename("printf.cvl")));
	}

	@Test
	public void printfBad() throws ABCException {
		assertFalse(ui.run("verify", filename("printfBad.cvl")));
	}

	@Test
	public void quantifiers() {
		assertTrue(ui.run("verify", filename("quantifiers.cvl")));
	}

	@Test
	public void scoping() throws ABCException {
		assertTrue(ui.run("verify", filename("scoping.cvl")));
	}

	@Test
	public void self() throws ABCException {
		assertTrue(ui.run("verify", filename("self.cvl")));
	}

	@Test
	public void sideEffects() throws ABCException {
		assertTrue(ui.run("verify", filename("sideEffects.cvl")));
	}

	@Test
	public void sizeOf() throws ABCException {
		assertTrue(ui.run("verify", filename("sizeOf.cvl")));
	}

	@Test
	public void struct() throws ABCException {
		assertTrue(ui.run("verify", filename("struct.cvl")));
	}

	@Test
	public void structArray() throws ABCException {
		assertTrue(ui.run("verify", filename("structArray.cvl")));
	}

	@Test
	public void structStruct() throws ABCException {
		assertTrue(ui.run("verify", filename("structStruct.cvl")));
	}

	@Test
	public void switchBlock() throws ABCException {
		assertTrue(ui.run("verify", filename("switch.cvl")));
	}

}