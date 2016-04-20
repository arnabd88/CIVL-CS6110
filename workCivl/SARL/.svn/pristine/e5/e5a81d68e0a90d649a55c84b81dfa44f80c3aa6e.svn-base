package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;

public class IntegerBitwiseOperationTest {
	private final static PrintStream OUT = System.out;
	private final static boolean DEBUG = false;
	private final static int INTEGER_BIT_LENGTH = 32;

	private SymbolicUniverse universe;
	// private SymbolicType intType;
	private SymbolicCompleteArrayType bitVectorType;
	private NumericExpression intMin; // integer -4
	private NumericExpression intNegFour; // integer -4
	private NumericExpression intNegOne; // integer -1
	private NumericExpression intZero; // integer 0
	private NumericExpression intPosOne; // integer 1
	private NumericExpression intMax; // integer -4

	// private NumericExpression x, y, z;
	// private StringObject x_obj, y_obj, z_obj; // "x", "y", "z"

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		// intType = universe.integerType();
		bitVectorType = universe.bitVectorType(INTEGER_BIT_LENGTH);
		intMin = universe.integer(Integer.MIN_VALUE);
		intNegFour = universe.integer(-4);
		intNegOne = universe.integer(-1);
		intZero = universe.integer(0);
		intPosOne = universe.integer(1);
		intMax = universe.integer(Integer.MAX_VALUE);

		// x_obj = universe.stringObject("x");
		// y_obj = universe.stringObject("y");
		// z_obj = universe.stringObject("z");
		// x = (NumericExpression) universe.symbolicConstant(x_obj, intType);
		// y = (NumericExpression) universe.symbolicConstant(y_obj, intType);
		// z = (NumericExpression) universe.symbolicConstant(z_obj, intType);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Debugging printing function
	 * 
	 * @param o
	 *            Target {@link Object} should be printed.
	 */
	private void p(Object o) {
		if (DEBUG) {
			OUT.println(o);
		}
	}

	/**
	 * Expression: 1 & 0; <br>
	 * Expected: 0;
	 */
	@Test
	public void bitand_concreteNumbers_intPosOne_intZero() {
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bv_intPosOne = universe.integer2Bitvector(intPosOne,
				bitVectorType);
		SymbolicExpression bitandResult = universe.bitand(bv_intZero,
				bv_intPosOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		NumericExpression expectedResult = universe.integer(0);

		p("Expresiion: 0 & 1");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult: " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: -1 & 1; <br>
	 * Expected: 1;
	 */
	@Test
	public void bitand_concreteNumbers_intNegOne_intPosOne() {
		SymbolicExpression bv_intPosOne = universe.integer2Bitvector(intPosOne,
				bitVectorType);
		SymbolicExpression bv_intNegOne = universe.integer2Bitvector(intNegOne,
				bitVectorType);
		SymbolicExpression bitandResult = universe.bitand(bv_intPosOne,
				bv_intNegOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		NumericExpression expectedResult = universe.integer(1);

		p("Expresiion: -1 & 1");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult: " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: -4 & 1; <br>
	 * Expected: -3;
	 */
	@Test
	public void bitor_concreteNumbers_intNegFour_intPosOne() {
		SymbolicExpression bv_intNegFour = universe.integer2Bitvector(
				intNegFour, bitVectorType);
		SymbolicExpression bv_intPosOne = universe.integer2Bitvector(intPosOne,
				bitVectorType);
		SymbolicExpression bitorResult = universe.bitor(bv_intNegFour,
				bv_intPosOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitorResult);
		NumericExpression expectedResult = universe.integer(-3);

		p("Expresiion: -4 & 1");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult: " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: ~0; <br>
	 * Expected: -1;
	 */
	@Test
	public void bitnot_intZero() {
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bitnotResult = universe.bitnot(bv_intZero);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitnotResult);
		NumericExpression expectedResult = universe.integer(-1);

		p("Expresiion: ~0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult: " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: ~(-2147483648); Integer.MIN_VALUE<br>
	 * Expected: 2147483647; Integer.MAX_VALUE
	 */
	@Test
	public void bitnot_intMin() {
		SymbolicExpression bv_intMin = universe.integer2Bitvector(intMin,
				bitVectorType);
		SymbolicExpression bitnotResult = universe.bitnot(bv_intMin);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitnotResult);
		NumericExpression expectedResult = intMax;

		p("Expresiion: ~(-2147483648)");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult: " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: ~2147483647; Integer.MAX_VALUE<br>
	 * Expected: -2147483648; Integer.MIN_VALUE
	 */
	@Test
	public void bitnot_intMax() {
		SymbolicExpression bv_intMax = universe.integer2Bitvector(intMax,
				bitVectorType);
		SymbolicExpression bitnotResult = universe.bitnot(bv_intMax);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitnotResult);
		NumericExpression expectedResult = intMin;

		p("Expresiion: ~0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult: " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}
}
