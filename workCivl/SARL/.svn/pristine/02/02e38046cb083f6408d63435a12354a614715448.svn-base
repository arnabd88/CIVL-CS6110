package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.PrintStream;
import java.util.Arrays;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;

public class SimplifyTest {

	static PrintStream out = System.out;

	static SymbolicUniverse universe = SARL.newStandardUniverse();

	static SymbolicIntegerType intType = universe.integerType();

	static NumericExpression zero = universe.integer(0);

	static NumericExpression one = universe.integer(1);

	static NumericExpression two = universe.integer(2);

	static NumericExpression three = universe.integer(3);

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void invalidInterval() {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		SymbolicConstant X = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("X"),
						universe.integerType()));
		// context: X<1 && 1<X
		BooleanExpression context = (BooleanExpression) universe.and(
				universe.lessThan((NumericExpression) X, universe.oneInt()),
				universe.lessThan(universe.oneInt(), (NumericExpression) X));
		Reasoner reasoner = universe.reasoner(context);
		// SARL crashes here
		Interval interval = reasoner.assumptionAsInterval(X);

		assertTrue(interval == null);
	}

	@Test
	public void simplify() {
		SymbolicUniverse univ = SARL.newStandardUniverse();
		SymbolicConstant X1 = (SymbolicConstant) univ.canonic(univ
				.symbolicConstant(univ.stringObject("X1"), univ.integerType()));
		SymbolicConstant X2 = (SymbolicConstant) univ.canonic(univ
				.symbolicConstant(univ.stringObject("X2"), univ.integerType()));
		BooleanExpression contex = (BooleanExpression) univ.canonic(univ
				.equals(univ.integer(4), univ.canonic(univ.multiply(
						(NumericExpression) X1, (NumericExpression) X2))));
		Reasoner reasoner;

		contex = (BooleanExpression) univ.canonic(univ.and(
				contex,
				(BooleanExpression) univ.canonic(univ.equals(X1,
						univ.integer(1)))));
		reasoner = univ.reasoner(contex);
		System.out.println(contex.toString());
		contex = reasoner.getReducedContext();
		System.out.println(contex.toString());
	}

	@Test
	public void test() {
		NumericExpression x = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("x"), intType);
		SymbolicCompleteArrayType arrayType = universe.arrayType(intType, x);
		NumericSymbolicConstant index = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"), intType);
		SymbolicExpression arrayLambda = universe.arrayLambda(arrayType,
				universe.lambda(index, index));

//		out.println(arrayLambda);
		out.println(universe);
		
		BooleanExpression context = universe.equals(x, three);
		Reasoner reasoner = universe.reasoner(context);
		SymbolicExpression simplifiedArrayLambda = reasoner
				.simplify(arrayLambda);
		SymbolicExpression concreteArray = universe.array(intType,
				Arrays.asList(zero, one, two));

		out.println(simplifiedArrayLambda);
		out.flush();

		assertEquals(concreteArray, simplifiedArrayLambda);
	}
	
	@Test
	public void divideTest(){
			NumericExpression a = (NumericExpression) universe.symbolicConstant(
					universe.stringObject("a"), intType);
			NumericExpression b = (NumericExpression) universe.symbolicConstant(
					universe.stringObject("a"), intType);
			BooleanExpression precon = universe.equals(universe.integer(3)
					, universe.divide(a, b));
			BooleanExpression predicate = universe.equals(a, 
					universe.multiply(b, universe.integer(3)));
			BooleanExpression e = universe.forall((SymbolicConstant)a, 
					universe.implies(precon, predicate));
			Reasoner r = universe.reasoner(universe.bool(true));
			r.isValid(e);
	}
	
}
