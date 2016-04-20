package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class LanguageFeaturesTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"languageFeatures");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void abstractFun() throws ABCException {
		assertTrue(ui.run("verify", filename("abstractFun.cvl")));
	}

	@Test
	public void abstractFunNoArg() throws ABCException {
		assertFalse(ui.run("verify", filename("abstractFunNoArg.cvl")));
	}

	@Test
	public void arrayLiteral() throws ABCException {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				filename("arrayLiteral.cvl")));
	}

	@Test
	public void arrayPointer() throws ABCException {
		assertTrue(ui.run("verify", filename("arrayPointer.cvl")));
	}

	@Test
	public void arrays() throws ABCException {
		assertTrue(ui.run("verify", filename("arrays.cvl")));
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
	public void badGuard() throws ABCException {
		assertFalse(ui.run("verify", filename("badGuard.cvl")));
	}

	/**
	 * This should be moved to test/dev.
	 */
	@Ignore
	@Test
	public void bigO() {
		assertTrue(ui.run("verify", filename("bigO.cvl")));
	}

	@Test
	public void bitwise() {
		assertTrue(ui.run("verify", filename("bitwise.cvl")));
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
	public void bundleTest() throws ABCException {
		assertTrue(ui.run("verify", filename("bundleTest.cvl")));
	}

	@Test
	public void bundleTestBad() throws ABCException {
		assertFalse(ui.run("verify", filename("bundleTestBad.cvl")));
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
	public void choose_int() throws ABCException {
		assertTrue(ui.run("verify", filename("choose_int.cvl")));
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
	public void forLoop() throws ABCException {
		assertTrue(ui.run("verify", filename("for.cvl")));
	}

	@Test
	public void functionPrototype() throws ABCException {
		assertTrue(ui.run("verify", filename("functionPrototype.cvl")));
	}

	@Test
	public void functionPrototypeBad() throws ABCException {
		assertFalse(ui.run("verify", filename("functionPrototypeBad.cvl")));
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
	public void pointerAdd() throws ABCException {
		assertTrue(ui.run("verify", filename("pointerAdd.cvl")));
	}

	@Test
	public void pointerAdd2() throws ABCException {
		assertTrue(ui.run("verify", filename("pointerAdd2.cvl")));
	}

	@Test
	public void pointerAddBad() throws ABCException {
		assertFalse(ui.run("verify", filename("pointerAddBad.cvl")));
	}

	@Test
	public void pointerAddBad2() throws ABCException {
		assertFalse(ui.run("verify", filename("pointerAddBad2.cvl")));
	}

	@Test
	public void pointerAddBad3() throws ABCException {
		assertFalse(ui.run("verify", filename("pointerAddBad3.c")));
	}

	@Test
	public void pointerAddBad4() throws ABCException {
		assertFalse(ui.run("verify", filename("pointerAddBad4.c")));
	}

	@Test
	public void pointerAddBad5() throws ABCException {
		assertFalse(ui.run("verify", filename("pointerAddBad5.c")));
	}

	@Test
	public void pointerAddBad6() throws ABCException {
		assertFalse(ui
				.run("verify -errorBound=2", filename("pointerAddBad6.c")));
	}

	@Test
	public void pointerAdd6() {
		assertTrue(ui.run("verify", filename("pointerAdd6.c")));
	}

	@Test
	public void pointerAddBad7() throws ABCException {
		assertFalse(ui.run("verify", filename("pointerAddBad7.c")));
	}

	@Test
	public void quantifiers() {
		assertTrue(ui.run("verify", filename("quantifiers.cvl")));
	}
	
	@Test
	public void quantifiersBad() {
		assertTrue(ui.run("verify", filename("quantifiersBad.cvl")));
	}

	@Test
	public void removedHeapPointer() throws ABCException {
		assertFalse(ui.run("verify", filename("removedHeapPointer.cvl")));
	}

	@Test
	public void scopeOperators() throws ABCException {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				filename("scopeOperators.cvl")));
	}

	@Test
	public void scoping() throws ABCException {
		assertFalse(ui.run("verify", filename("scoping.cvl")));
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
		assertTrue(ui.run("verify", filename("sizeof.cvl")));
	}

	@Test
	public void spawnFoo() throws ABCException {
		assertFalse(ui.run("verify", filename("spawnFoo.cvl")));
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

	@Test
	public void union() throws ABCException {
		assertTrue(ui.run("verify", filename("union.cvl")));
	}

	@Test
	public void enum1() throws ABCException {
		assertTrue(ui.run("verify", filename("enum1.cvl")));
	}

	@Test
	public void enum2() throws ABCException {
		assertTrue(ui.run("verify", filename("enum2.cvl")));
	}

	@Test
	public void functionPointer() throws ABCException {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				filename("functionPointer.cvl")));
	}

	@Test
	public void undefPointer() throws ABCException {
		assertFalse(ui.run("verify", filename("undefPointer.cvl")));
	}

	@Test
	public void undefHeapPointer() throws ABCException {
		assertFalse(ui.run("verify", filename("undefHeapPointer.cvl")));
	}

	@Test
	public void sideEffectLoop() throws ABCException {
		assertTrue(ui.run("verify", filename("sideEffectLoop.cvl")));
	}

	@Test
	public void assignInput() throws ABCException {
		assertFalse(ui.run("verify", filename("assignInput.cvl")));
	}

	@Test
	public void inputBad() throws ABCException {
		assertFalse(ui.run("verify", filename("inputBad.cvl")));
	}

	@Test
	public void outputBad() throws ABCException {
		assertFalse(ui.run("verify", filename("outputBad.cvl")));
	}

	@Test
	public void procNull() throws ABCException {
		assertTrue(ui.run("verify", filename("procNull.cvl")));
	}

	@Test
	public void functionBad() throws ABCException {
		assertFalse(ui.run("verify", filename("functionBad.cvl")));
	}

	@Test
	public void intToBool() throws ABCException {
		assertTrue(ui.run("verify", filename("intToBool.cvl")));
	}

	@Test
	public void twoDpointerTest() throws ABCException {
		assertTrue(ui.run("verify", filename("2dpointerTest.cvl")));
	}

	@Test
	public void memoryLeak() throws ABCException {
		assertFalse(ui.run("verify", filename("memoryLeak.cvl")));
	}

	@Test
	public void processLeak() throws ABCException {
		assertFalse(ui.run("verify", filename("processLeak.cvl")));
	}

	@Test
	public void comma() throws ABCException {
		assertTrue(ui.run("verify", "-inputn=5", filename("comma.cvl")));
	}

	@Test
	public void assignIntWtReal() {
		assertTrue(ui.run("verify", filename("assignIntWtReal.cvl")));
	}

	@Test
	public void civlPragma() throws ABCException {
		assertTrue(ui.run("verify", "-inputNB=5", filename("civlPragma.cvl")));
	}

	@Test
	public void civlFor() throws ABCException {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				filename("civlfor.cvl")));
	}

	@Test
	public void civlParfor() throws ABCException {
		assertTrue(ui.run("verify", "-enablePrintf=false",
				filename("civlParfor.cvl")));
	}

	@Test
	public void pointerSub() {
		assertTrue(ui.run("verify", filename("pointerSubtraction.cvl")));
	}

	@Test
	public void pointerSubBad() {
		assertFalse(ui.run("verify", filename("pointerSubtractionBad.cvl")));
	}

	@Test
	public void pointerSubBad2() {
		assertFalse(ui.run("verify", filename("pointerSubtractionBad2.cvl")));
	}

	@Test
	public void stringTest() {
		assertTrue(ui.run("verify", filename("stringTest.cvl")));
	}

	@Test
	public void int2char() {
		assertTrue(ui.run("verify", filename("int2char.cvl")));
	}

	@Test
	public void int2charBad() {
		assertFalse(ui.run("verify", filename("int2charBad.cvl")));
	}

	@Test
	public void int2charBad2() {
		assertFalse(ui.run("verify", filename("int2charBad2.cvl")));
	}

	@Test
	public void include1() {
		assertFalse(ui.run("verify", "-userIncludePath=" + rootDir.getPath(),
				filename("include1.cvl")));
	}

	@Test
	public void procBound() {
		assertFalse(ui.run("verify", "-procBound=10", "-showTransitions=false",
				"-showSavedStates=false", filename("procBound.cvl")));
	}

	@Test
	public void not() {
		assertTrue(ui.run("verify", filename("not.cvl")));
	}

	@Test
	public void noopBad() {
		assertFalse(ui.run("verify ", filename("noopBad.cvl")));
	}

	@Test
	public void pointerAdd1() {
		assertTrue(ui.run("verify", filename("pointerAdd1.cvl")));
		assertFalse(ui.run("verify -DWRONG", filename("pointerAdd1.cvl")));
		assertTrue(ui.run("verify -DARRAY", filename("pointerAdd1.cvl")));
		assertFalse(ui.run("verify -DARRAY -DWRONG",
				filename("pointerAdd1.cvl")));

	}

	@Test
	public void int2float() {
		assertTrue(ui.run("verify ", filename("int2float.cvl")));
	}

	@Test
	public void staticVar() {
		assertTrue(ui.run("verify ", filename("staticVar.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
