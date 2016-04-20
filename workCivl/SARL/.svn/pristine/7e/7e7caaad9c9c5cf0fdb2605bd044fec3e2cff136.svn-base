package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Standard equivalence in propositional logic.
 * 
 * @author sili
 *
 */
public class BooleanReasonDevTest {
	public final static PrintStream out = System.out;
	public final static boolean debug = true;
	private SymbolicUniverse universe;
	private BooleanExpression A, B, C;
	private StringObject a_obj, b_obj, c_obj;
	private SymbolicType boolType;
	private BooleanExpression trueExpr, falseExpr;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		a_obj = universe.stringObject("A");
		b_obj = universe.stringObject("B");
		c_obj = universe.stringObject("C");
		boolType = universe.booleanType();
		A = (BooleanExpression) universe.symbolicConstant(a_obj, boolType);
		B = (BooleanExpression) universe.symbolicConstant(b_obj, boolType);
		C = (BooleanExpression) universe.symbolicConstant(c_obj, boolType);
		trueExpr = universe.bool(true);
		falseExpr = universe.bool(false);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * (A ^ B) equiv (B ^ A)
	 */
	@Test
	public void commutativityAndTest() {
		BooleanExpression e1 = universe.and(A, B);
		BooleanExpression e2 = universe.and(B, A);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * (A v B) equiv (B v A)
	 */
	@Test
	public void commutativityOrTest() {
		BooleanExpression e1 = universe.or(A, B);
		BooleanExpression e2 = universe.or(B, A);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A ^ (B ^ C) equiv (A ^ B) ^ C
	 */
	@Test
	public void associativityAndTest() {
		BooleanExpression e1 = universe.and(A, universe.and(B, C));
		BooleanExpression e2 = universe.and(universe.and(A, B), C);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A v (B v C) equiv (A v B) v C
	 */
	@Test
	public void associativityOrTest() {
		BooleanExpression e1 = universe.or(A, universe.or(B, C));
		BooleanExpression e2 = universe.or(universe.or(A, B), C);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A ^ (A v B) equiv A
	 */
	@Test
	public void absorptionTest1() {
		BooleanExpression e1 = universe.and(A, universe.or(A, B));
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e2), reasoner.simplify(e1));
	}

	/**
	 * A v (A ^ B) equiv A
	 */
	@Test
	public void absorptionTest2() {
		BooleanExpression e1 = universe.or(A, universe.and(A, B));
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e2), reasoner.simplify(e1));
	}

	/**
	 * A ^ (not A) equiv false
	 */
	@Test
	public void complement1() {
		BooleanExpression e = universe.and(A, universe.not(A));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e is " + e);
		}
		assertEquals(falseExpr, reasoner.simplify(e));
	}

	/**
	 * A v (not A) equiv true
	 */
	@Test
	public void complement2() {
		BooleanExpression e = universe.or(A, universe.not(A));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e is " + e);
		}
		assertEquals(trueExpr, reasoner.simplify(e));
	}

	/**
	 * A ^ (B v C) equiv (A ^ B) v (A ^ C)
	 */
	@Test
	public void distributivityTest1() {
		BooleanExpression e1 = universe.and(A, universe.or(B, C));
		BooleanExpression e2 = universe.or(universe.and(A, B),
				universe.and(A, C));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A v (B ^ C) equiv (A v B) ^ (A v C)
	 */
	@Test
	public void distributivityTest2() {
		BooleanExpression e1 = universe.or(A, universe.and(B, C));
		BooleanExpression e2 = universe.and(universe.or(A, B),
				universe.or(A, C));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * not (A ^ B) equiv (not A) v (not B)
	 */
	@Test
	public void DeMorganLawTest1() {
		BooleanExpression e1 = universe.not(universe.and(A, B));
		BooleanExpression e2 = universe.or(universe.not(A), universe.not(B));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * not (A v B) equiv (not A) ^ (not B)
	 */
	@Test
	public void DeMorganLawTest2() {
		BooleanExpression e1 = universe.not(universe.or(A, B));
		BooleanExpression e2 = universe.and(universe.not(A), universe.not(B));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A -> B equiv (not A) v B
	 */
	@Test
	public void DeMorganLawTest3() {
		BooleanExpression e1 = universe.implies(A, B);
		BooleanExpression e2 = universe.or(universe.not(A), B);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * not A equiv A -> false
	 */
	@Test
	public void DeMorganLawTest4() {
		BooleanExpression e1 = universe.not(A);
		BooleanExpression e2 = universe.implies(A, falseExpr);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * not (not A) equiv A
	 */
	@Test
	public void doubleNegationTest() {
		BooleanExpression e1 = universe.not(universe.not(A));
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A ^ true equiv A
	 */
	@Test
	public void neutralElementTest1() {
		BooleanExpression e1 = universe.and(A, trueExpr);
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A v false equiv A
	 */
	@Test
	public void neutralElementTest2() {
		BooleanExpression e1 = universe.or(A, falseExpr);
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A ^ false equiv false
	 */
	@Test
	public void absorptionElementTest1() {
		BooleanExpression e1 = universe.and(A, falseExpr);
		BooleanExpression e2 = falseExpr;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A v true equiv true
	 */
	@Test
	public void absorptionElementTest2() {
		BooleanExpression e1 = universe.or(A, trueExpr);
		BooleanExpression e2 = trueExpr;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * (A -> B) -> A equiv A
	 * 
	 * <pre>
	 * proof:
	 * (A -> B) -> A equiv !(!A v B) v A
	 * 				 equiv (A ^ !B) v A
	 * 				 equiv A v (A ^ !B)
	 * 				 equiv A
	 * </pre>
	 */
	@Test
	public void extraEquiv() {
		BooleanExpression e1 = universe.implies(universe.implies(A, B), A);
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e2), reasoner.simplify(e1));
	}
}
