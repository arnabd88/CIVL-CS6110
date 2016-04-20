package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class IntegerArithmeticDevTest {
	public final static PrintStream out = System.out;
	public final static boolean debug = false;
	private SymbolicUniverse universe;
	private NumericExpression negOneInt; // integer -1
	private NumericExpression x;
	private StringObject x_obj; // "x", "y", "z"
	private SymbolicType intType;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		negOneInt = universe.integer(-1);
		x_obj = universe.stringObject("x");
		intType = universe.integerType();
		x = (NumericExpression) universe.symbolicConstant(x_obj, intType);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Negative exponent power test.
	 * Has been moved to realArithmaticTest
	 */
	@Ignore
	@Test
	public void negativeExponentPowerTest() {
		NumericExpression e = universe.power(x, negOneInt);

		assertEquals(universe.divide(universe.oneInt(), x), e);
	}
	
	/**
	 * This is an integer test (need to be moved)
	 * <x,y> = 2^x * (2y + 1) -1
	 * x and y are integers
	 * x > 0 && y > 0
	 */
	@Test
	public void pairFucTest(){
//		universe.setShowProverQueries(true);
//		NumericExpression int_zero = universe.integer(0);
		NumericExpression int_one = universe.integer(1);
		NumericExpression int_two = universe.integer(2);
		
		NumericExpression int_five = universe.integer(5);
		
//		NumericExpression int_ten = universe.integer(10);
		SymbolicType integerType = universe.integerType();
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("x"), integerType);
		NumericExpression y = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("y"), integerType);
		NumericExpression twoPowerX = universe.power(int_two, x);
		NumericExpression twoYPlusOne = universe.add(universe.multiply(int_two, y), int_one);
		NumericExpression xyPair = universe.subtract(universe.multiply(twoPowerX, twoYPlusOne), int_one);

		Reasoner r = universe.reasoner(universe.equals(xyPair, int_five));
		BooleanExpression e1 = universe.and(universe.equals(x, int_one), universe.equals(y, int_one));
		ValidityResult result1 = r.valid(e1);
		assertEquals(ResultType.YES, result1.getResultType());
//		
//		BooleanExpression pre = universe.and(universe.lessThanEquals(int_zero, x), universe.lessThanEquals(int_zero, y));
//		Reasoner r = universe.reasoner(universe.and(universe.equals(xyPair, int_ten), pre));
//		BooleanExpression e2 = universe.and(universe.equals(x, int_zero), universe.equals(y, int_five));
//		ValidityResult result2 = r.valid(e2);
//		assertEquals(ResultType.YES, result2.getResultType());
	}
	
	//TODO:
	// cvc4 exception...
	@Test
	public void powerTest(){
		universe.setShowProverQueries(true);
		SymbolicType integerType = universe.integerType();
		NumericExpression int_two = universe.integer(2);
		NumericExpression int_three = universe.integer(3);
		NumericExpression int_eight = universe.integer(8);
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("x"), integerType);
		NumericExpression twoPowerX = universe.power(int_two, x); // 2^x
		BooleanExpression assumption = universe.equals(twoPowerX, int_eight);// 2^x = 8
//		System.out.println("assumption:"+assumption);
		Reasoner r = universe.reasoner(assumption);
		BooleanExpression deduction = universe.equals(x, int_three); // x == 3?
		ValidityResult result = r.valid(deduction);
		assertEquals(ResultType.YES, result.getResultType());
	}
}