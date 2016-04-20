package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Boolean tests methods found in edu.udel.cis.vsl.sarl.IF package.
 * CoreUniverse.java, SymbolicUniverse.java
 */
public class BooleanTest {
	public final static PrintStream out = System.out;
	public final static boolean debug = false;
	private SymbolicUniverse universe;
	private BooleanExpression f1; // "false expression"
	private BooleanExpression f2;
	private BooleanExpression t1; // "true expression"
	private BooleanExpression t2;
	private BooleanExpression trueExpr, falseExpr;
	private NumericExpression x, y;
	private StringObject x_obj, y_obj; // "x", "y", "z"
	private SymbolicType intType;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		f1 = universe.falseExpression(); // "false expression"
		f2 = universe.falseExpression();
		t1 = universe.trueExpression(); // "true expression"
		t2 = universe.trueExpression();
		trueExpr = universe.bool(true);
		falseExpr = universe.bool(false);
		x_obj = universe.stringObject("x");
		y_obj = universe.stringObject("y");
		intType = universe.integerType();
		x = (NumericExpression) universe.symbolicConstant(x_obj, intType);
		y = (NumericExpression) universe.symbolicConstant(y_obj, intType);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Testing the "extractBoolean" method, if the given expression has a
	 * concrete Boolean value, this returns it, else it returns null.
	 */
	@Test
	public void testExtractBoolean() {
		BooleanExpression nullExpression = null;

		assertEquals(true, universe.extractBoolean(trueExpr));
		assertEquals(false, universe.extractBoolean(falseExpr));
		assertEquals(null, universe.extractBoolean(nullExpression));
	}

	/**
	 * Testing the "Returns the boolean literal" method, returns symbolic
	 * expression true or false.
	 */
	@Test
	public void testBooleanIiteral() {
		BooleanExpression p = universe.trueExpression();
		BooleanExpression q = universe.falseExpression();

		assertEquals(trueExpr, p);
		assertEquals(falseExpr, q);
	}

	/**
	 * Testing the logical negation for the given argument.
	 */
	@Test
	public void testNot() {
		BooleanExpression nf = universe.not(f1);
		BooleanExpression nnf = universe.not(nf);

		assertEquals(trueExpr, nf);
		assertEquals(falseExpr, nnf);
	}

	/**
	 * Testing the the conjunction of the two given arguments.
	 */
	@Test
	public void testAndTwoArgs() {

		BooleanExpression tt = universe.and(t1, t2);
		BooleanExpression ff = universe.and(f1, f2);
		BooleanExpression tf = universe.and(f1, t1);

		assertEquals(trueExpr, tt); // true iff both true
		assertEquals(falseExpr, ff);
		assertEquals(falseExpr, tf);
	}

	/**
	 * Testing the conjunction of the expressions in the given array args. If
	 * the length of args is 0, the resulting expression is equivalent to
	 * "true".
	 */
	@Test
	public void testAndIterable() {
		List<BooleanExpression> booleanList1 = new ArrayList<BooleanExpression>();
		List<BooleanExpression> booleanList2 = new ArrayList<BooleanExpression>();
		List<BooleanExpression> booleanList3 = new ArrayList<BooleanExpression>();
		List<BooleanExpression> booleanEmptyList = new ArrayList<BooleanExpression>();

		booleanList1.add(trueExpr);
		booleanList1.add(trueExpr);
		booleanList1.add(trueExpr);
		booleanList2.add(trueExpr);
		booleanList2.add(trueExpr);
		booleanList2.add(falseExpr);
		booleanList3.add(falseExpr);
		booleanList3.add(falseExpr);
		booleanList3.add(falseExpr);

		assertEquals(trueExpr, universe.and(booleanList1));
		assertEquals(falseExpr, universe.and(booleanList2));
		assertEquals(falseExpr, universe.and(booleanList3));
		assertEquals(trueExpr, universe.and(booleanEmptyList));
	}

	/**
	 * Testing the disjunction of the two given arguments.
	 */
	@Test
	public void testOrTwoArgs() {
		BooleanExpression tt = universe.or(t1, t2);
		BooleanExpression ff = universe.or(f1, f2);
		BooleanExpression tf = universe.or(f1, t1);

		assertEquals(trueExpr, tt);
		assertEquals(falseExpr, ff); // false iff both false
		assertEquals(trueExpr, tf);
	}

	/**
	 * Testing the disjunction of the expressions in the given array args. If
	 * the length of args is 0, the resulting expression is equivalent to
	 * "false".
	 */
	@Test
	public void testOrIterable() {
		List<BooleanExpression> booleanList1 = new ArrayList<BooleanExpression>();
		List<BooleanExpression> booleanList2 = new ArrayList<BooleanExpression>();
		List<BooleanExpression> booleanList3 = new ArrayList<BooleanExpression>();
		List<BooleanExpression> booleanEmptyList = new ArrayList<BooleanExpression>();

		booleanList1.add(trueExpr);
		booleanList1.add(trueExpr);
		booleanList1.add(trueExpr);
		booleanList2.add(trueExpr);
		booleanList2.add(trueExpr);
		booleanList2.add(falseExpr);
		booleanList3.add(falseExpr);
		booleanList3.add(falseExpr);
		booleanList3.add(falseExpr);

		assertEquals(trueExpr, universe.or(booleanList1));
		assertEquals(trueExpr, universe.or(booleanList2));
		assertEquals(falseExpr, universe.or(booleanList3));
		assertEquals(falseExpr, universe.or(booleanEmptyList));
	}

	/**
	 * Testing "p implies q", i.e., p=>q.
	 */
	@Test
	public void testImplies() {
		BooleanExpression tt = universe.implies(t1, t2);
		BooleanExpression ff = universe.implies(f1, f2);
		BooleanExpression ft = universe.implies(f1, t1);
		BooleanExpression tf = universe.implies(t2, f2);

		assertEquals(trueExpr, tt);
		assertEquals(trueExpr, ff);
		assertEquals(trueExpr, ft);
		assertEquals(falseExpr, tf); // false iff T->F
	}

	/**
	 * Testing "p is equivalent to q", i.e., p<=>q.
	 */
	@Test
	public void testEquiv() {
		BooleanExpression tt = universe.equiv(t1, t2);
		BooleanExpression ff = universe.equiv(f1, f2);
		BooleanExpression ft = universe.equiv(f1, t1);
		BooleanExpression tf = universe.equiv(t2, f2);

		assertEquals(trueExpr, tt); // true iff both the same
		assertEquals(trueExpr, ff);
		assertEquals(falseExpr, ft);
		assertEquals(falseExpr, tf);
	}

	/**
	 * Testing boolean "less than", i.e., return true if arg0 < arg1.
	 * 
	 * <pre>
	 * n1 = x - 1;
	 * n2 = x + 1;
	 * </pre>
	 */
	@Test
	public void lessThan() {
		NumericExpression n1 = universe.subtract(x, universe.oneInt());
		NumericExpression n2 = universe.add(x, universe.oneInt());
		BooleanExpression e1 = universe.lessThan(n2, n1);
		BooleanExpression e2 = universe.lessThan(n1, n2);

		assertEquals(falseExpr, e1);
		assertEquals(trueExpr, e2);
	}

	/**
	 * Testing boolean "less than equals", i.e., return true if arg0 <= arg1.
	 *
	 * <pre>
	 * n1 = x - 1;
	 * n2 = x + 1;
	 * </pre>
	 */
	@Test
	public void lessThanEquals() {
		NumericExpression n1 = universe.add(x, universe.oneInt());
		NumericExpression n2 = universe.subtract(x, universe.oneInt());
		BooleanExpression result1 = universe.lessThanEquals(x, n1);
		BooleanExpression result2 = universe.lessThanEquals(n2, x);
		BooleanExpression result3 = universe.lessThanEquals(x, x);

		assertEquals(trueExpr, result1);
		assertEquals(trueExpr, result2);
		assertEquals(trueExpr, result3);
	}

	/**
	 * Returns true if the first argument is 'equal' to the second argument and
	 * returns false otherwise.
	 * 
	 * <pre>
	 * n1 = x + 1;
	 * n2 = (1 * x ^ 2) + x;
	 * n3 = x * y + x;
	 * r1 = (x + y) / x;
	 * </pre>
	 */
	@Test
	public void equals() {
		NumericExpression n1 = universe.add(x, universe.oneInt());
		NumericExpression n2 = universe.add(
				universe.multiply(universe.oneInt(), universe.multiply(x, x)),
				x);
		NumericExpression n3 = universe.add(
				universe.multiply(universe.oneInt(), universe.multiply(x, y)),
				x);
		NumericExpression r1 = universe.divide(universe.add(x, y), x);

		BooleanExpression b0 = universe.equals(x, n1);
		BooleanExpression b5 = universe.neq(x, n1);
		BooleanExpression b1 = universe.equals(x, n2);
		BooleanExpression b2 = universe.equals(x, n3);
		BooleanExpression b3 = universe.equals(x, x);
		BooleanExpression b4 = universe.equals(universe.oneInt(), r1);

		if (debug) {
			out.println("b1=" + b1);
			out.println("b2=" + b2);
			out.println("b4=" + b4);
		}
		assertEquals(falseExpr, b0);
		assertEquals(trueExpr, b3);
		assertEquals(trueExpr, b5); // test neq method
	}
}
