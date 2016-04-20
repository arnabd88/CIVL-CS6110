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
package edu.udel.cis.vsl.sarl.expr.cnf;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.IF.BooleanExpressionFactory;
import edu.udel.cis.vsl.sarl.expr.IF.ExpressionFactory;
import edu.udel.cis.vsl.sarl.expr.IF.Expressions;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

/**
 * CnfFactoryTest is used to test the code mostly in CnfFactory. This includes
 * all of the various binary comparators and other methods for comparing and
 * determining expressions.
 * 
 */
public class CnfFactoryTest {

	// private static SymbolicUniverse sUniverse = Universes.newIdealUniverse();

	private static SymbolicType booleanType;
	private static SymbolicTypeFactory stf;
	private static ObjectFactory of;
	private static ExpressionFactory ef;

	private static BooleanExpressionFactory factory;

	static StringObject string1;
	static StringObject string2;
	static StringObject string3;

	private static NumericSymbolicConstant x; // real symbolic constant "X"
	private static BooleanSymbolicConstant b;

	private static BooleanSymbolicConstant p, q;

	static NumberFactory numberFactory = Numbers.REAL_FACTORY;

	/**
	 * setUp() initializes many of the variables used in the following tests.
	 * 
	 * @throws Exception
	 */
	@Before
	public void setUpBeforeClass() {
		FactorySystem system = PreUniverses.newIdealFactorySystem2();

		factory = system.booleanFactory();
		stf = system.typeFactory();
		of = system.objectFactory();
		ef = system.expressionFactory();
		booleanType = stf.booleanType();
		p = factory.booleanSymbolicConstant(of.stringObject("p"));
		q = factory.booleanSymbolicConstant(of.stringObject("q"));
	}

	/**
	 * tearDown()
	 * 
	 * @throws Exception
	 */
	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Check !(p&&q) equals (!p)||(!q).
	 */
	@Test
	public void notAnd() {
		BooleanExpression e1 = factory.not(factory.and(p, q));
		BooleanExpression e2 = factory.or(factory.not(p), factory.not(q));

		assertEquals(e1, e2);
	}

	/**
	 * Testing for code in CnfFactoryNot() makes sure that the function not
	 * actually returns not(value)
	 */
	@Test
	public void notTest() {
		BooleanExpressionFactory bef = Expressions.newCnfFactory(stf, of);
		BooleanExpression testingfalse = factory.falseExpr();
		StringObject pobject = of.stringObject("a");
		StringObject qobject = of.stringObject("b");
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression p = (BooleanExpression) ef.symbolicConstant(pobject,
				booleanType);
		BooleanExpression q = (BooleanExpression) ef.symbolicConstant(qobject,
				booleanType);
		BooleanExpression foralltruechk = bef.exists(b, testingfalse);
		BooleanExpression EXISTS = bef
				.booleanExpression(SymbolicOperator.EXISTS, foralltruechk);
		BooleanPrimitive cnf2 = (BooleanPrimitive) EXISTS;
		BooleanExpression existschk = bef.forall(b, testingtrue);
		BooleanExpression FORALL = bef
				.booleanExpression(SymbolicOperator.FORALL, existschk);
		BooleanPrimitive cnf3 = (BooleanPrimitive) FORALL;
		BooleanExpression andtrue = bef.and(p, q);
		BooleanExpression ortrue = bef.or(p, q);
		BooleanExpression nottrue = bef.not(q);
		BooleanExpression foralltrue = bef.forall(b, testingtrue);
		BooleanExpression existstrue = bef.exists(b, testingfalse);

		// Use DeMorgan's rules logic to create same functions using ands or ors
		// to test
		assertEquals(bef.or(bef.not(p), bef.not(q)), bef.not(andtrue));
		assertEquals(bef.and(bef.not(p), bef.not(q)), bef.not(ortrue));
		assertEquals(q, bef.not(nottrue));

		// for not(forall) since it is not, check with reverse(i.e. exists)
		assertEquals(cnf2.argument(0), bef.not(foralltrue));

		// for not(exists)
		assertEquals(cnf3.argument(0), bef.not(existstrue));
	}

	/**
	 * Testing for code in CnfFactoryNot(). Uses longer groups of values to
	 * ensure that even in long sets, not will still return not(value)
	 * 
	 */
	@Test
	public void cnFFactoryNotTest() {
		BooleanExpressionFactory bef = Expressions.newCnfFactory(stf, of);
		BooleanExpression testingfalse = factory.falseExpr();
		StringObject pobject = of.stringObject("a");
		StringObject qobject = of.stringObject("b");
		BooleanExpression p = (BooleanExpression) ef.symbolicConstant(pobject,
				booleanType);
		BooleanExpression q = (BooleanExpression) ef.symbolicConstant(qobject,
				booleanType);
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression andtrue = bef.and(p, q);
		BooleanExpression ortrue = bef.or(p, q);
		BooleanExpression nottrue = bef.not(q);
		BooleanExpression foralltrue = bef.forall(b, testingtrue);
		BooleanExpression existstrue = bef.exists(b, testingfalse);
		BooleanExpression foralltruechk = bef.exists(b, testingfalse);
		BooleanExpression EXISTS = bef
				.booleanExpression(SymbolicOperator.EXISTS, foralltruechk);
		BooleanPrimitive cnf2 = (BooleanPrimitive) EXISTS;
		BooleanExpression existschk = bef.forall(b, testingtrue);
		BooleanExpression FORALL = bef
				.booleanExpression(SymbolicOperator.FORALL, existschk);
		BooleanPrimitive cnf3 = (BooleanPrimitive) FORALL;

		assertEquals(bef.or(bef.not(p), bef.not(q)), bef.not(andtrue));
		assertEquals(bef.and(bef.not(p), bef.not(q)), bef.not(ortrue));
		assertEquals(q, bef.not(nottrue));

		assertEquals(cnf2.argument(0), bef.not(foralltrue));

		// for not(exists)
		assertEquals(cnf3.argument(0), bef.not(existstrue));
	}

	/**
	 * Testing for code in CnfFactoryOr() this includes combination and
	 * simplification of boolean variables
	 * 
	 */
	@Test
	public void orTest() {
		CnfFactory bef = (CnfFactory) Expressions.newCnfFactory(stf, of);
		StringObject pobject = of.stringObject("p");
		StringObject qobject = of.stringObject("q");
		StringObject robject = of.stringObject("r");
		BooleanExpression p = (BooleanExpression) ef.symbolicConstant(pobject,
				booleanType);
		BooleanExpression q = (BooleanExpression) ef.symbolicConstant(qobject,
				booleanType);
		BooleanExpression r = (BooleanExpression) ef.symbolicConstant(robject,
				booleanType);
		BooleanExpression falseExpr = bef.falseExpr();
		BooleanExpression trueExpr = bef.trueExpr();
		BooleanExpression qandtrue = bef.and(q, trueExpr);
		BooleanExpression pandfalse = bef.and(p, falseExpr);
		BooleanExpression qortrue = bef.or(q, bef.not(p));
		BooleanExpression porfalse = bef.or(p, r);
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression testingfalse = factory.falseExpr();

		// testing for various combinations of true and false and and or results
		if (bef.getBooleanExpressionSimplification()) {
			assertEquals(trueExpr,
					(bef.or(p, bef.or(q, bef.or(bef.not(p), r)))));
			assertEquals(trueExpr, bef.or(qortrue, porfalse));
		}

		assertEquals(falseExpr, bef.and(bef.not(p), p));
		assertEquals(falseExpr, bef.and(p, bef.not(p)));
		assertEquals(bef.or(bef.not(p), r),
				(bef.or(bef.not(p), bef.and(p, r))));

		assertEquals(bef.and(p, r), bef.or(bef.and(p, r), bef.and(r, p)));
		assertEquals(bef.or(bef.or(p, r), p), bef.or(r, p));
		assertEquals(bef.or(bef.or(p, r), bef.or(q, r)),
				bef.or(r, bef.or(q, p)));
		assertEquals(testingtrue, bef.or(p, bef.not(p)));
		assertEquals(testingtrue, bef.or(bef.not(p), p));
		assertEquals(testingfalse, bef.not(bef.or(bef.not(p), p)));
		assertEquals(q, bef.or(qandtrue, pandfalse));
	}

	/**
	 * Testing for code in CnfFactoryOr() with simplification on.
	 * 
	 */
	@Test
	public void orSimplifyTest() {
		CnfFactory bef = (CnfFactory) Expressions.newCnfFactory(stf, of);
		bef.setBooleanExpressionSimplification(true);
		StringObject pobject = of.stringObject("p");
		StringObject qobject = of.stringObject("q");
		StringObject robject = of.stringObject("r");
		BooleanExpression p = (BooleanExpression) ef.symbolicConstant(pobject,
				booleanType);
		BooleanExpression q = (BooleanExpression) ef.symbolicConstant(qobject,
				booleanType);
		BooleanExpression r = (BooleanExpression) ef.symbolicConstant(robject,
				booleanType);
		BooleanExpression falseExpr = bef.falseExpr();
		BooleanExpression trueExpr = bef.trueExpr();
		BooleanExpression qandtrue = bef.and(q, trueExpr);
		BooleanExpression pandfalse = bef.and(p, falseExpr);
		BooleanExpression qortrue = bef.or(q, bef.not(p));
		BooleanExpression porfalse = bef.or(p, r);
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression testingfalse = factory.falseExpr();

		// testing for various combinations of true and false and and or results
		if (bef.getBooleanExpressionSimplification()) {
			assertEquals(trueExpr,
					(bef.or(p, bef.or(q, bef.or(bef.not(p), r)))));
			assertEquals(trueExpr, bef.or(qortrue, porfalse));
		}

		assertEquals(falseExpr, bef.and(bef.not(p), p));
		assertEquals(falseExpr, bef.and(p, bef.not(p)));
		assertEquals(bef.or(bef.not(p), r),
				(bef.or(bef.not(p), bef.and(p, r))));

		assertEquals(bef.and(p, r), bef.or(bef.and(p, r), bef.and(r, p)));
		assertEquals(bef.or(bef.or(p, r), p), bef.or(r, p));
		assertEquals(bef.or(bef.or(p, r), bef.or(q, r)),
				bef.or(r, bef.or(q, p)));
		assertEquals(testingtrue, bef.or(p, bef.not(p)));
		assertEquals(testingtrue, bef.or(bef.not(p), p));
		assertEquals(testingfalse, bef.not(bef.or(bef.not(p), p)));
		assertEquals(q, bef.or(qandtrue, pandfalse));
	}

	/**
	 * Tests CnfFactory and(bool boolExpr1, bool boolExpr2) method. ensures that
	 * and correctly makes (expr1 && expr2) as well anding groups of sets
	 */
	@Test
	public void andTrueExprTest() {
		BooleanExpressionFactory bef = Expressions.newCnfFactory(stf, of);
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression testingfalse = factory.falseExpr();
		BooleanExpression falseExpr = bef.falseExpr();
		BooleanExpression trueExpr = bef.trueExpr();

		assertEquals(testingtrue, bef.and(testingtrue, testingtrue));
		assertEquals(testingtrue, bef.and(trueExpr, testingtrue));
		assertEquals(testingfalse, bef.and(trueExpr, testingfalse));
		assertEquals(testingfalse, bef.and(testingfalse, trueExpr));
		assertEquals(testingfalse, bef.and(falseExpr, testingtrue));
		assertEquals(testingfalse, bef.and(testingtrue, falseExpr));
	}

	/**
	 * Tests CnfFactory or(bool boolExpr1, bool boolExpr2) method. Tests for
	 * combinations of statements, and simplifications for or
	 */
	@Test
	public void orTrueExprTest() {
		BooleanExpressionFactory bef = Expressions.newCnfFactory(stf, of);

		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression testingfalse = factory.falseExpr();

		BooleanExpression falseExpr = bef.falseExpr();
		BooleanExpression trueExpr = bef.trueExpr();

		assertEquals(testingtrue, bef.or(testingtrue, testingtrue));
		assertEquals(testingtrue, bef.or(trueExpr, testingtrue));
		assertEquals(testingtrue, bef.or(trueExpr, testingfalse));
		assertEquals(testingtrue, bef.or(falseExpr, testingtrue));
		assertEquals(testingfalse, bef.or(testingfalse, falseExpr));
		// System.out.println(bef.and(p, bef.or(q, bef.not(q))));
	}

	/**
	 * Testing for code in CnfFactoryNot() makes sure not(false) is true
	 */
	@Test
	public void booleannotTest() {
		CnfFactory test = new CnfFactory(stf, of);
		BooleanExpressionFactory bef = Expressions.newCnfFactory(stf, of);
		BooleanExpression falseEx = bef.falseExpr();

		assertEquals(false, test.not(falseEx).isFalse());
	}

	/**
	 * Testing for code in CnfFactoryforall(). Tests to ensure all combinations
	 * of forall(values) return their correct output.
	 */
	@Test
	public void forAllTest() {
		CnfFactory test = new CnfFactory(stf, of);
		BooleanExpressionFactory bef = Expressions.newCnfFactory(stf, of);
		BooleanExpression falseEx = bef.falseExpr();
		BooleanExpression trueEx = bef.trueExpr();
		assertEquals(true, test.forall(x, falseEx).isFalse());
		assertEquals(false, test.forall(x, falseEx).isTrue());
		assertEquals(true, test.forall(x, trueEx).isTrue());
		assertEquals(false, test.forall(x, trueEx).isFalse());
	}

	/**
	 * Testing for code in CnfFactoryExists() Tests to make sure if something
	 * exists, then exists(something) = true
	 */
	@Test
	public void existsTest() {
		CnfFactory test = new CnfFactory(stf, of);
		BooleanExpressionFactory bef = Expressions.newCnfFactory(stf, of);
		BooleanExpression falseEx = bef.falseExpr();
		BooleanExpression trueEx = bef.trueExpr();
		BooleanExpression b = bef.or(trueEx, falseEx);

		assertEquals(true, test.exists(x, b).isTrue());
		assertEquals(true, test.exists(x, falseEx).isFalse());
		assertEquals(false, test.exists(x, falseEx).isTrue());
		assertEquals(true, test.exists(x, trueEx).isTrue());
		assertEquals(false, test.exists(x, trueEx).isFalse());
	}

	/**
	 * Testing for code in CnfSymbolicConstant() Tests to make sure the super is
	 * working correctly. This is for tostring() and .name
	 */
	@Test
	public void cnfSymbolicConstantTest() {
		StringObject name = of.stringObject("Hello");
		CnfFactory Test = new CnfFactory(stf, of);
		CnfSymbolicConstant hellotest = (CnfSymbolicConstant) Test
				.booleanSymbolicConstant(name);
		StringObject hellomsg = of.stringObject("Hello");
		StringObject hellomsgfalse = of.stringObject("hello");

		assertEquals(hellomsg, hellotest.name());
		assertNotEquals(hellomsgfalse, hellotest.name());
		assertEquals("Hello", hellotest.toString());
		assertNotEquals("hello", hellotest.toString());
	}

	@Test
	public void unsatisfiableTest() {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		NumericExpression two = universe.integer(2);
		SymbolicConstant X = universe.symbolicConstant(
				universe.stringObject("X"), universe.integerType());
		BooleanExpression clause1 = universe.lessThanEquals(
				universe.divide((NumericExpression) X, two), universe.oneInt());
		BooleanExpression clause2 = universe.lessThanEquals(universe.integer(3),
				(NumericExpression) X);

		BooleanExpression result = universe
				.reasoner(universe.and(clause1, clause2)).getReducedContext();
		System.out.println(result);

		// want X=3.
		// need to reason as follows:
		// a div b <= c ==>
		// assume a>=0, b>0
		// a = q*b + r
		// q>=0, 0<=r<b
		// q=(a-r)/b=a/b-r/b
		// (a/b)-1<q<=a/b

		// X/2>=3/2
		// X div 2 > (X/2)-1 >= 3/2-1 >= .5 -> X div 2 >= 1
		// -> X div 2 = 1
		// X/2<X div 2 + 1 = 2 -> X<4 -> X=3

		// Here is how to do it:

		// To get a bound on a%b, where b>0 is constant:
		// first, get a bound on a. if a>=0: a%b is in [0,b-1].
		// if a<=0 a%b in [1-b,0]. In any case: a%b in [1-b,b-1].

		// if a bound I1 is created on a div b:
		// 1. get bound I2 on a%b as above (if not already present)
		// 2. use fact that a=(a div b)*b+a%b to get bound on a:
		// b*I1+I2

	}
}
