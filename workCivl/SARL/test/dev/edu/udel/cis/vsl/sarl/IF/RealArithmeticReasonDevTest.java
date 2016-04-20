package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class RealArithmeticReasonDevTest {
	private static boolean debug = true;
	private static PrintStream out = System.out;
	private SymbolicUniverse universe;
	private NumericExpression negOne, one, two;
	private StringObject a_obj; // "a"
	private StringObject b_obj; // "b"
	private StringObject c_obj; // "c"
	private StringObject d_obj; // "d"
	private NumericExpression a;
	private NumericExpression b;
	private NumericExpression c;
	private NumericExpression d;
	private SymbolicType realType;
	private BooleanExpression trueExpr;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		realType = universe.realType();
		negOne = universe.rational(-1);
		one = universe.rational(1);
		two = universe.rational(2);
		a_obj = universe.stringObject("a");
		b_obj = universe.stringObject("b");
		c_obj = universe.stringObject("c");
		d_obj = universe.stringObject("d");
		a = (NumericExpression) universe.symbolicConstant(a_obj, realType);
		b = (NumericExpression) universe.symbolicConstant(b_obj, realType);
		c = (NumericExpression) universe.symbolicConstant(c_obj, realType);
		d = (NumericExpression) universe.symbolicConstant(d_obj, realType);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * TODO under development ab = (c+1)*(c-1) && a = c + 1 ===> b = c - 1
	 * 
	 * c != -1
	 */
	@Test
	public void RealArithmeticReason1() {
		NumericExpression c2MinusOne = universe.multiply(universe.add(c, one),
				universe.subtract(c, one));
		NumericExpression cPlusOne = universe.add(c, one); // cPlusOne = c+1
		NumericExpression aTimesB = universe.multiply(a, b); // aTimesB = a*b
		NumericExpression cSubOne = universe.subtract(c, one); // cSubOne = c-1
		BooleanExpression assumption = universe.and(universe.neq(c, negOne),
				universe.and(universe.equals(aTimesB, c2MinusOne),
						universe.equals(a, cPlusOne)));
		// a*b = c^2 -1 && a = c+1
		Reasoner r = universe.reasoner(assumption);
		BooleanExpression be = universe.equals(cSubOne, b);

		if (debug) {
			out.println(aTimesB + "=" + c2MinusOne);
			out.println(a + "=" + cPlusOne);
			out.println(cSubOne + "=?" + b);
		}
		// assertEquals(true, r.isValid(be));
		ValidityResult result = r.valid(be);
		assertEquals(ResultType.MAYBE, result.getResultType());
	}

	/**
	 * TODO under development a = (b+1)*(c+2) && d = a/(b+1) ===> d = c+2
	 */
	@Test
	public void RealArithmeticReason3() {
		NumericExpression bPlusOne = universe.add(b, one);
		NumericExpression cPlusTwo = universe.add(c, two);
		NumericExpression bAddOneTimescPlusTwo = universe.multiply(bPlusOne,
				cPlusTwo);
		NumericExpression aDivideBPlusOne = universe.divide(a, bPlusOne);
		BooleanExpression assumption = universe.and(universe.neq(b, negOne),
				universe.and(universe.equals(a, bAddOneTimescPlusTwo),
						universe.equals(d, aDivideBPlusOne)));
		Reasoner r = universe.reasoner(assumption);
		BooleanExpression eq = universe.equals(d, universe.add(c, two));
		ValidityResult result = r.valid(eq);

		if (debug) {
			out.println(a + "=" + bAddOneTimescPlusTwo);
			out.println(d + "=" + aDivideBPlusOne);
		}

		assertEquals(ResultType.MAYBE, result.getResultType());
	}

	/**
	 * 
	 * a = (b+1)*(b+1) && c = b+1 ===> a = c^2
	 */
	@Test
	public void RealArithmeticReason2() {
		NumericExpression bPlusOne = universe.add(b, one);
		NumericExpression bPlusOneSqure = universe.multiply(bPlusOne, bPlusOne);
		NumericExpression c2 = universe.multiply(c, c);
		Reasoner r = universe
				.reasoner(universe.and(universe.equals(c, bPlusOne),
						universe.equals(a, bPlusOneSqure)));
		BooleanExpression eq = universe.equals(a, c2);
		ValidityResult result = r.valid(eq);

		assertEquals(ResultType.MAYBE, result.getResultType());
	}

	/**
	 * Symbolic real modulus. true : (a^b)*(a^c)=a^(b+c)
	 */
	@Test
	public void addExponentTest() {
		NumericExpression e1 = universe.multiply(universe.power(a, b),
				universe.power(a, c));
		NumericExpression e2 = universe.power(a, universe.add(b, c));
		Reasoner reasoner = universe.reasoner(trueExpr);
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * Negative exponent power test.
	 */
	@Test
	public void negativeExponentPowerTest() {
		NumericExpression e = universe.power(a, negOne);

		assertEquals(universe.divide(universe.oneReal(), a), e);
	}
}
