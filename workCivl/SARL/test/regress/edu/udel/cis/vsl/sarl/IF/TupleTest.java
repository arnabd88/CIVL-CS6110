package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * This test suite is created for functions related with
 * {@link SymbolicExpression}s with the type of {@link SymbolicTupleType}, and
 * all test cases do <strong>NOT</strong> include {@link NullPointerException}
 * situations.
 * 
 * @author wwh
 *
 */
public class TupleTest {

	private static boolean DEBUG = false;
	
	private SymbolicUniverse sUniverse;

	private SymbolicTupleType tupleType_int, tupleType_real, tupleType_int_int,
			tupleType_int_int_int;

	private NumericExpression int_0, int_1, int_2, real_half;

	private IntObject index_0, index_1, index_2;

	@Before
	public void setUp() throws Exception {
		sUniverse = SARL.newStandardUniverse();
		tupleType_real = sUniverse.tupleType(
				sUniverse.stringObject("tuple_real"),
				Arrays.asList(new SymbolicType[] { sUniverse.realType() }));
		tupleType_int = sUniverse.tupleType(
				sUniverse.stringObject("tuple_int"),
				Arrays.asList(new SymbolicType[] { sUniverse.integerType() }));
		tupleType_int_int = sUniverse.tupleType(
				sUniverse.stringObject("tuple_int_int"),
				Arrays.asList(new SymbolicType[] { sUniverse.integerType(),
						sUniverse.integerType() }));
		tupleType_int_int_int = sUniverse.tupleType(
				sUniverse.stringObject("tuple_int_int_int"),
				Arrays.asList(new SymbolicType[] { sUniverse.integerType(),
						sUniverse.integerType(), sUniverse.integerType() }));
		int_0 = sUniverse.integer(0);
		int_1 = sUniverse.integer(1);
		int_2 = sUniverse.integer(2);
		real_half = sUniverse.rational(1, 2);
		index_0 = sUniverse.intObject(0);
		index_1 = sUniverse.intObject(1);
		index_2 = sUniverse.intObject(2);
	}

	@After
	public void tearDown() throws Exception {
	}
	
	private void p(Object o){
		if (DEBUG) System.out.println(o.toString());
	}
	
	private void p(String s){
		if (DEBUG) System.out.println(s);
	}

	// Interface:CoreUniverse
	// Function: tuple
	@Test(expected = SARLException.class)
	public void tuple_fieldTypeAndComponents_SizeMismatched() {
		sUniverse.tuple(tupleType_int,
				Arrays.asList(new SymbolicExpression[] { int_1, int_2 }));
	}

	@Test(expected = SARLException.class)
	public void tuple_fieldTypeAndComponents_TypeMismatched() {
		sUniverse.tuple(tupleType_real,
				Arrays.asList(new SymbolicExpression[] { int_1 }));
	}

	@Test
	public void tuple_contruct() {
		sUniverse.tuple(tupleType_int,
				Arrays.asList(new SymbolicExpression[] { int_0 }));
		sUniverse.tuple(tupleType_int_int,
				Arrays.asList(new SymbolicExpression[] { int_0, int_0 }));
	}

	// Interface:CoreUniverse
	// Function: tupleRead, TupleWrite
	@Test(expected = SARLException.class)
	public void tupleWrite_TypeMismatched() {
		SymbolicExpression tuple_int_int = sUniverse.tuple(tupleType_int_int,
				Arrays.asList(new SymbolicExpression[] { int_0, int_1 }));
		sUniverse.tupleWrite(tuple_int_int, index_0, real_half);
	}

	@Test
	public void tupleWrite_sameValue() {
		SymbolicExpression tuple_int_int = sUniverse.tuple(tupleType_int_int,
				Arrays.asList(new SymbolicExpression[] { int_0, int_1 }));
		sUniverse.tupleWrite(tuple_int_int, index_0, int_0);
	}

	@Test
	public void tupleWrite_differentValue() {
		SymbolicExpression tuple_int_int = sUniverse.tuple(tupleType_int_int,
				Arrays.asList(new SymbolicExpression[] { int_0, int_1 }));
		sUniverse.tupleWrite(tuple_int_int, index_1, int_0);
	}

	@Test
	public void tupleWrite_denseWrite_single_component() {
		SymbolicExpression denseTuple = sUniverse.symbolicConstant(
				sUniverse.stringObject("denseTuple"), tupleType_int);
		sUniverse.tupleWrite(denseTuple, index_0, int_0);
		sUniverse.tupleWrite(denseTuple, index_0, int_1);
	}

	@Test
	public void tupleWrite_denseWrite_more_components() {
		SymbolicExpression denseTuple = sUniverse.symbolicConstant(
				sUniverse.stringObject("denseTuple"), tupleType_int_int);
		denseTuple = sUniverse.tupleWrite(denseTuple, index_0, int_0);
		denseTuple = sUniverse.tupleWrite(denseTuple, index_0, int_0);
		denseTuple = sUniverse.tupleWrite(denseTuple, index_1, int_0);
		denseTuple = sUniverse.tupleWrite(denseTuple, index_1, int_1);
	}

	@Test(expected = SARLException.class)
	public void tupleRead_TypeMismatched() {
		sUniverse.tupleRead(int_1, index_0);
	}

	@Test
	public void tupleRead() {
		SymbolicExpression tuple_int_int = sUniverse.tuple(tupleType_int_int,
				Arrays.asList(new SymbolicExpression[] { int_0, int_1 }));
		SymbolicExpression componet_0 = sUniverse.tupleRead(tuple_int_int,
				index_0);
		SymbolicExpression componet_1 = sUniverse.tupleRead(tuple_int_int,
				index_1);
		assertEquals(int_0, componet_0);
		assertEquals(int_1, componet_1);
	}

	@Test
	public void tupleRead_denseWrite_single_component() {
		SymbolicExpression denseTuple = sUniverse.symbolicConstant(
				sUniverse.stringObject("denseTuple"), tupleType_int);

		denseTuple = sUniverse.tupleWrite(denseTuple, index_0, int_0);
		assertEquals(int_0, sUniverse.tupleRead(denseTuple, index_0));
		denseTuple = sUniverse.tupleWrite(denseTuple, index_0, int_1);
		assertEquals(int_1, sUniverse.tupleRead(denseTuple, index_0));
	}

	@Test
	public void tupleRead_denseWrite_more_components() {
		SymbolicExpression denseTuple = sUniverse.symbolicConstant(
				sUniverse.stringObject("denseTuple"), tupleType_int_int_int);
		denseTuple = sUniverse.tupleWrite(denseTuple, index_0, int_0);
		assertEquals(int_0, sUniverse.tupleRead(denseTuple, index_0));
		denseTuple = sUniverse.tupleWrite(denseTuple, index_1, int_1);
		assertEquals(int_1, sUniverse.tupleRead(denseTuple, index_1));
		denseTuple = sUniverse.tupleWrite(denseTuple, index_2, int_2);
		assertEquals(int_2, sUniverse.tupleRead(denseTuple, index_2));
	}

	@Test
	public void tupleRead_denseWrite_NOT_initialized_component_ALL() {
		SymbolicExpression denseTuple = sUniverse.symbolicConstant(
				sUniverse.stringObject("denseTuple"), tupleType_int_int_int);
		sUniverse.tupleRead(denseTuple, index_0);
	}

	@Test
	public void tupleRead_denseWrite_NOT_initialized_component_Part1() {
		SymbolicExpression denseTuple = sUniverse.symbolicConstant(
				sUniverse.stringObject("denseTuple"), tupleType_int_int);
		denseTuple = sUniverse.tupleWrite(denseTuple, index_0, int_0);
		sUniverse.tupleRead(denseTuple, index_1);
	}

	@Test
	public void tupleRead_denseWrite_NOT_initialized_component_Part2() {
		SymbolicExpression denseTuple = sUniverse.symbolicConstant(
				sUniverse.stringObject("denseTuple"), tupleType_int_int_int);
		denseTuple = sUniverse.tupleWrite(denseTuple, index_2, int_2);
		sUniverse.tupleRead(denseTuple, index_1);
		sUniverse.tupleRead(denseTuple, index_0);
		denseTuple = sUniverse.tupleWrite(denseTuple, index_1, int_1);
		sUniverse.tupleRead(denseTuple, index_0);
		denseTuple = sUniverse.tupleWrite(denseTuple, index_0, int_0);
	}

	// Interface:CoreUniverse
	// Function: equals
	@Test
	public void tuple_Equals() {
		SymbolicExpression tuple_int_int1 = sUniverse.tuple(tupleType_int_int,
				Arrays.asList(new SymbolicExpression[] { int_1, int_1 }));
		SymbolicExpression tuple_int_int2 = sUniverse.tuple(tupleType_int_int,
				Arrays.asList(new SymbolicExpression[] { int_1, int_2 }));
		SymbolicExpression tuple_int_int3 = sUniverse.tupleWrite(
				tuple_int_int2, index_1, int_1);
		assertEquals(tuple_int_int1, tuple_int_int1);
		assertEquals(tuple_int_int1, tuple_int_int3);
		assert sUniverse.equals(tuple_int_int1, tuple_int_int1).isTrue();
		assert sUniverse.equals(tuple_int_int1, tuple_int_int2).isFalse();
	}

	/**
	 * <pre>
	 * Tuple type: variable_ref=<tupleType_int, reference>
	 * Tuple: {{1}, [1]}
	 * substituter map: {<{1}, {2}>}
	 * Result after substitution: {{2}, [1]}
	 * </pre>
	 */
	@Test
	public void tuple_substitute() {
		SymbolicTupleType tupleType = sUniverse.tupleType(
				sUniverse.stringObject("variable_ref"),
				Arrays.asList(tupleType_int, sUniverse.referenceType()));
		ReferenceExpression self = sUniverse.identityReference();
		ReferenceExpression arrayEle1 = sUniverse.arrayElementReference(self,
				int_1);
		SymbolicExpression tupleInt1 = sUniverse.tuple(tupleType_int,
				Arrays.asList(int_1));
		SymbolicExpression tupleInt2 = sUniverse.tuple(tupleType_int,
				Arrays.asList(int_2));
		SymbolicExpression tuple = sUniverse.tuple(tupleType,
				Arrays.asList(tupleInt1, arrayEle1));
		Map<SymbolicExpression, SymbolicExpression> oldToNew = new HashMap<>();

		oldToNew.put(tupleInt1, tupleInt2);

		UnaryOperator<SymbolicExpression> substituter = sUniverse
				.mapSubstituter(oldToNew);

		tuple = substituter.apply(tuple);
		// field 0 should be updated
		assertEquals(sUniverse.tupleRead(tuple, index_0), tupleInt2);
		// field 1 remains unchanged
		assertEquals(sUniverse.tupleRead(tuple, index_1), arrayEle1);
	}

	/**
	 * <pre>
	 * Tuple type: variable_ref=<tupleType_int, reference>
	 * Tuple: {{0}, [0]}
	 * substituter map: {<{0}, [1]>, <[0], {1}>}
	 * Result after substitution: {[1], {1}}
	 * </pre>
	 */
	@Test(expected=SARLException.class)
	public void tuple_substitute2() {
		SymbolicTupleType tupleType_Ref_TupleInt = sUniverse.tupleType(
				sUniverse.stringObject("variable_ref_tupleInt"),
				Arrays.asList(tupleType_int, sUniverse.referenceType()));
		ReferenceExpression self = sUniverse.identityReference();
		ReferenceExpression arrayEle0 = sUniverse.arrayElementReference(self,
				int_0);
		ReferenceExpression arrayEle1 = sUniverse.arrayElementReference(self,
				int_1);
		SymbolicExpression tupleInt0 = sUniverse.tuple(tupleType_int,
				Arrays.asList(int_0));
		SymbolicExpression tupleInt1 = sUniverse.tuple(tupleType_int,
				Arrays.asList(int_1));
		SymbolicExpression tuple = sUniverse.tuple(tupleType_Ref_TupleInt,
				Arrays.asList(tupleInt0, arrayEle0));
		Map<SymbolicExpression, SymbolicExpression> oldToNew = new HashMap<>();

		oldToNew.put(tupleInt0, arrayEle1);
		oldToNew.put(arrayEle0, tupleInt1);

		UnaryOperator<SymbolicExpression> substituter = sUniverse
				.mapSubstituter(oldToNew);

		p("Before Substitution: ");
		p(tuple.atomString());
		p(((SymbolicTupleType)tuple.type()).sequence());
		tuple = substituter.apply(tuple);
		p("After Substitution: ");
		p(tuple.atomString());
		p(((SymbolicTupleType)tuple.type()).sequence());
		// field 0 should be changed from tupleInt0 to arrayEle1
		assertEquals(arrayEle1, sUniverse.tupleRead(tuple, index_0));
		// field 1 should be changed from arrayEle0 to tupleInt1
		assertEquals(tupleInt1, sUniverse.tupleRead(tuple, index_1));
	}
}
