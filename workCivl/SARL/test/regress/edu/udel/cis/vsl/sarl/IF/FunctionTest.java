package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class FunctionTest {
	public final static PrintStream out = System.out;
	public final static boolean debug = true;
	private SymbolicUniverse universe;
	private SymbolicType integerType;
	private SymbolicType realType;
	private SymbolicCompleteArrayType arrayType;
	private NumericSymbolicConstant x, a, b,c,d;
	private NumericExpression one, two, four;
	
	
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		integerType = universe.integerType();
		realType = universe.realType();
		x = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("x"), integerType);
		arrayType = universe.arrayType(integerType, x);
		a = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("a"), integerType);
		b = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("b"), integerType);
		c = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("c"), integerType);
		d = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("d"), integerType);
		one = universe.integer(1);
		two = universe.integer(2);
		four = universe.integer(4);
	}
	
	@After
	public void tearDown() throws Exception {
	}
	
	@Test
	public void arrayLambdaTest() {
		SymbolicExpression function1;
		SymbolicExpression arrayL1;
		SymbolicExpression function2;
		SymbolicExpression arrayL2;
		
		function1 = universe.lambda(a, universe.multiply(a, a));
		arrayL1 = universe.arrayLambda(arrayType, function1);
		function2 = universe.lambda(b, universe.add(b, one));
		arrayL2 = universe.arrayLambda(arrayType, function2);

		assertEquals(universe.multiply(two, two), universe.arrayRead(arrayL1, two));
		assertEquals(universe.add(two, one), universe.arrayRead(arrayL2, universe.integer(2)));
	}
	
	@Test
	public void applyTest(){
		SymbolicExpression function1;
		function1 = universe.lambda(a, universe.multiply(a, a));
		SymbolicExpression function2;
		List<SymbolicExpression> args1 = new ArrayList<SymbolicExpression>();
		args1.add(two);
		function2 = universe.lambda(b, universe.multiply(b, (NumericExpression)universe.apply(function1, args1)));
		List<SymbolicExpression> args2 = new ArrayList<SymbolicExpression>();
		args2.add(four);
		SymbolicExpression r = universe.apply(function2, args2);
		if(debug){
			out.println(r);
		}
		assertEquals(universe.multiply(four, universe.multiply(two, two)), r);
	}
	
	/**
	 * test function type
	 */
	@Test
	public void applyTest2(){
		SymbolicConstant f1;
		SymbolicFunctionType functionType1 = universe.functionType(
				Arrays.asList(new SymbolicType[] {integerType, integerType}), realType);
		f1 = universe.symbolicConstant(universe.stringObject("f1"), functionType1);
		SymbolicExpression r = universe.apply((SymbolicExpression)f1, 
				Arrays.asList(new SymbolicExpression[] {a, b}));
		System.out.println(r);
		assertEquals(realType, r.type());
	}
	
	/**
	 * TODO move to function reason test
	 * f(a,b) = c
	 * g(a,b) = d
	 * ==>
	 * h(c,d) = h(f(a,b), g(a,b))
	 */
	@Test
	public void applyReasonTest1(){
		SymbolicConstant f1; //f
		SymbolicConstant f2; //g
		SymbolicConstant f3; //h
		SymbolicFunctionType functionType1 = universe.functionType(
				Arrays.asList(new SymbolicType[] {integerType, integerType}), integerType);
		f1 = universe.symbolicConstant(universe.stringObject("f1"), functionType1);
		f2 = universe.symbolicConstant(universe.stringObject("f2"), functionType1);
		f3 = universe.symbolicConstant(universe.stringObject("f3"), functionType1);
		SymbolicExpression r1 = universe.apply((SymbolicExpression)f3, 
				Arrays.asList(new SymbolicExpression[] {c, d})); //h(c,d)
		SymbolicExpression f_a_b = universe.apply((SymbolicExpression)f1, 
				Arrays.asList(new SymbolicExpression[] {a, b})); //f(a,b)
		SymbolicExpression g_a_b = universe.apply((SymbolicExpression)f2, 
				Arrays.asList(new SymbolicExpression[] {a, b})); //g(a,b)
		SymbolicExpression r2 = universe.apply((SymbolicExpression)f3, 
				Arrays.asList(new SymbolicExpression[] {f_a_b, g_a_b})); //h(f(a,b), g(a,b))
		
		Reasoner reasoner = universe.reasoner(universe.and(universe.equals(c, f_a_b), 
				universe.equals(d, g_a_b)));
		BooleanExpression eq = universe.equals(r1, r2);
		ValidityResult result = reasoner.valid(eq);
		assertEquals(result.getResultType(), ResultType.YES);
	}
	
}
