/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
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
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class IntegerArithmeticReasonDevTest {
	public final static PrintStream out = System.out;
	public final static boolean debug = false;
	private SymbolicUniverse universe;
	private StringObject u_obj, x_obj, y_obj, z_obj; // "u", "x", "y", "z"
	private SymbolicType integerType;
	private NumericSymbolicConstant u, x, y, z; // integer symbolic constant
	private NumericExpression negOneInt, threeInt, fiveInt;
	private BooleanExpression trueExpr, falseExpr;
	private BooleanExpression assumption;
	private Reasoner reasoner;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		u_obj = universe.stringObject("u");
		x_obj = universe.stringObject("x");
		y_obj = universe.stringObject("y");
		z_obj = universe.stringObject("z");
		integerType = universe.integerType();
		u = (NumericSymbolicConstant) universe.symbolicConstant(u_obj,
				integerType);
		x = (NumericSymbolicConstant) universe.symbolicConstant(x_obj,
				integerType);
		y = (NumericSymbolicConstant) universe.symbolicConstant(y_obj,
				integerType);
		z = (NumericSymbolicConstant) universe.symbolicConstant(z_obj,
				integerType);
		negOneInt = universe.integer(-1);
		threeInt = universe.integer(3);
		fiveInt = universe.integer(5);
		trueExpr = universe.bool(true);
		falseExpr = universe.bool(false);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * u < 3 && u >=2: u -> 2
	 */
	@Test
	public void simplifyIntTight1() {
		BooleanExpression assumption = universe.and(
				universe.lessThan(u, universe.integer(3)),
				universe.lessThanEquals(universe.integer(2), u));
		Reasoner reasoner = universe.reasoner(assumption);

		assertEquals(universe.integer(2), reasoner.simplify(u));
		assertEquals(trueExpr, reasoner.getReducedContext());
	}

	/**
	 * u < 3 && u >1: u -> 2
	 */
	@Test
	public void simplifyIntTight2() {
		BooleanExpression assumption = universe.and(
				universe.lessThan(u, universe.integer(3)),
				universe.lessThan(universe.integer(1), u));
		Reasoner reasoner = universe.reasoner(assumption);

		assertEquals(universe.integer(2), reasoner.simplify(u));
		assertEquals(trueExpr, reasoner.getReducedContext());
	}

	/**
	 * u<3 && u>2 : contradiction
	 */
	@Test
	public void contradict1() {
		BooleanExpression assumption = universe.and(
				universe.lessThan(u, universe.integer(3)),
				universe.lessThan(universe.integer(2), u));
		Reasoner reasoner = universe.reasoner(assumption);

		assertEquals(u, reasoner.simplify(u));
		assertEquals(falseExpr, reasoner.getReducedContext());
	}

	/**
	 * u=2 : a{5,6,7}[u]->7
	 */
	@Test
	public void simplifyArrayRead() {
		SymbolicExpression a = universe.symbolicConstant(
				universe.stringObject("a"), universe.arrayType(integerType));

		a = universe.arrayWrite(a, universe.integer(0), universe.integer(5));
		a = universe.arrayWrite(a, universe.integer(1), universe.integer(6));
		a = universe.arrayWrite(a, universe.integer(2), universe.integer(7));

		SymbolicExpression read = universe.arrayRead(a, u);
		BooleanExpression assumption = universe.equals(u, universe.integer(2));
		Reasoner reasoner = universe.reasoner(assumption);

		assertEquals(universe.integer(7), reasoner.simplify(read));
		assertEquals(trueExpr, reasoner.getReducedContext());
	}

	/**
	 * Integer division. true : 2(u/2) -> 2(u/2)
	 */
	@Test
	public void simplifyIntDivNo() {
		SymbolicExpression e = universe.multiply(universe.integer(2),
				universe.divide(u, universe.integer(2)));
		Reasoner reasoner = universe.reasoner(trueExpr);

		assertEquals(e, reasoner.simplify(e));
	}

	/**
	 * Integer division. true : (2u)/2 -> u
	 */
	@Test
	public void simplifyIntDivYes() {
		SymbolicExpression e = universe.divide(
				universe.multiply(universe.integer(2), u), universe.integer(2));
		Reasoner reasoner = universe.reasoner(trueExpr);

		assertEquals(u, reasoner.simplify(e));
	}

	/**
	 * Integer modulus. true : 0 <= u/3 <=1 -> u <= 5
	 */
	@Test
	public void simplifyIntDivTest() {
		BooleanExpression assumption = universe.and(
				universe.lessThanEquals(universe.zeroInt(),
						universe.divide(u, threeInt)),
				universe.lessThanEquals(universe.divide(u, threeInt),
						universe.oneInt()));
		reasoner = universe.reasoner(assumption);
		BooleanExpression e1 = universe.lessThanEquals(u, fiveInt);
		ValidityResult result1 = reasoner.valid(e1);

		assertEquals(ResultType.YES, result1.getResultType());
	}

	/**
	 * Integer division test.
	 * 
	 * Assumption: 0 <= u/3 <= 1.
	 * 
	 * Query: u >= 0
	 * 
	 * Expected result: NO. Counterexample: -1.
	 */
	@Test
	public void simplifyIntDivTest2() {
		BooleanExpression assumption = universe.and(
				universe.lessThanEquals(universe.zeroInt(),
						universe.divide(u, threeInt)),
				universe.lessThanEquals(universe.divide(u, threeInt),
						universe.oneInt()));
		reasoner = universe.reasoner(assumption);
		BooleanExpression e2 = universe.lessThanEquals(universe.zeroInt(), u);
		ValidityResult result2 = reasoner.valid(e2);

		assertEquals(ResultType.NO, result2.getResultType());
	}

	/**
	 * Integer modulus. true : (2u)%2 -> 0 for all u;
	 */
	@Test
	public void simplifyIntMod() {
		SymbolicExpression e = universe.modulo(
				universe.multiply(universe.integer(2), u), universe.integer(2));
		reasoner = universe.reasoner(trueExpr);

		assertEquals(universe.zeroInt(), reasoner.simplify(e));
	}

	/**
	 * Integer modulus. u >= 0 ==> (2u + 1) % 2 simplifies to 1
	 */
	@Test
	public void simplifyIntMod2() {
		assumption = universe.lessThanEquals(universe.zeroInt(), u);
		reasoner = universe.reasoner(assumption);
		SymbolicExpression e = universe
				.modulo(universe.add(universe.multiply(universe.integer(2), u),
						universe.oneInt()), universe.integer(2));

		assertEquals(universe.oneInt(), reasoner.simplify(e));
	}

	/**
	 * Integer modulus. u<0 ==> (2u + 1) % 2 simplifies to -1.
	 */
	@Test
	public void simplifyNegMod() {
		assumption = universe.lessThan(u, universe.zeroInt());
		reasoner = universe.reasoner(assumption);
		SymbolicExpression e = universe
				.modulo(universe.add(universe.multiply(universe.integer(2), u),
						universe.oneInt()), universe.integer(2));

		assertEquals(negOneInt, reasoner.simplify(e));
	}

	// When evaluating x%constant: if x is a Monomial c*m,
	// (c*m)%d = ((c%d)*m)%d, and (c1*m1 + c2*m2)%d =...
	// (x^n)%d = ((x%d)^n)%d. In short, apply %d to all
	// constants...
	// (a*b)%d = ((a%d)*b)%d
	// (a+b)%d = ((a%d)+b)%d

	// /**
	// * Symbolic Integer modulus. true : ((x%z)*y)%z -> (x*y)%z
	// */
	// @Test
	// public void simplifySymbolicMod() {
	// SymbolicExpression e1 = universe
	// .modulo(universe.multiply(universe.modulo(x, z), y), z);
	// SymbolicExpression e2 = universe.modulo(universe.multiply(x, y), z);
	// reasoner = universe.reasoner(trueExpr);
	//
	// assertEquals(e2, reasoner.simplify(e1));
	// }

	// /**
	// * Symbolic Integer modulus. true : ((x%z)+y)%z -> (x+y)%z
	// */
	// @Test
	// public void simplifySymbolicMod2() {
	// SymbolicExpression e1 = universe
	// .modulo(universe.add(universe.modulo(x, z), y), z);
	// SymbolicExpression e2 = universe.modulo(universe.add(x, y), z);
	// reasoner = universe.reasoner(trueExpr);
	// if (debug) {
	// out.println(e1);
	// out.println(e2);
	// }
	//
	// assertEquals(e2, reasoner.simplify(e1));
	// }

	// /**
	// * Symbolic Integer modulus. true : ((x%z)^y)%z -> (x^y)%z
	// */
	// @Test
	// public void simplifySymbolicMod3() {
	// SymbolicExpression e1 = universe
	// .modulo(universe.power(universe.modulo(x, z), y), z);
	// SymbolicExpression e2 = universe.modulo(universe.power(x, y), z);
	// reasoner = universe.reasoner(trueExpr);
	// if (debug) {
	// out.println(e1);
	// out.println(e2);
	// }
	//
	// assertEquals(e2, reasoner.simplify(e1));
	// }

	// y has to have real type:
	// /**
	// * Symbolic Integer modulus. negative exponent power test
	// */
	// @Test
	// public void negativeExponentPowerTest() {
	// NumericExpression e = universe.multiply(x,
	// universe.power(y, negOneInt));
	// if (debug) {
	// out.println(e);
	// }
	// }

	// /**
	// * Symbolic Integer modulus. true : x/y = x*(y^-1)
	// */
	// @Test
	// public void divideToPowerTest() {
	// NumericExpression e1 = universe.divide(x, y);
	// NumericExpression e2 = universe.multiply(x,
	// universe.power(y, negOneInt));
	// reasoner = universe.reasoner(trueExpr);
	//
	// assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	// }

	/**
	 * Symbolic Integer power. true : (x^y)*(x^z)=x^(y+z)
	 */
	@Test
	public void addExponentTest() {
		NumericExpression e1 = universe.multiply(universe.power(x, y),
				universe.power(x, z));
		NumericExpression e2 = universe.power(x, universe.add(y, z));
		reasoner = universe.reasoner(trueExpr);

		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}
	
	/**
	 * Symbolic Integer modulus. true : (x^y)^z=x^(y*z)
	 */
	@Test
	public void exponentTest() {
		NumericExpression e1 = universe.power(universe.power(x, y), z);
		NumericExpression e2 = universe.power(x, universe.multiply(y, z));
		reasoner = universe.reasoner(trueExpr);

		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}
	
	/**
	 * Symbolic Integer modulus. true : x^0=0
	 */
	@Test
	public void exponentTest1() {
		//NumericExpression e1 = universe.power(universe.power(x, y), z);
		NumericExpression e2 = universe.power(x, universe.zeroInt());
		reasoner = universe.reasoner(trueExpr);

		assertEquals(universe.oneInt(), reasoner.simplify(e2));
	}
}
