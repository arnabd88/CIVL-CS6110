package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class ArrayReasonTest {
	private static PrintStream out = System.out;
	
	private SymbolicUniverse universe;
	private StringObject a_obj, b_obj, i_obj, j_obj, k_obj, m_obj; 
	private NumericExpression zero, one, two, three, five, six;
	private SymbolicType integerType;
	private SymbolicArrayType arrayType2D;
	private SymbolicArrayType arrayType;
	private SymbolicExpression intArr_a;
	private SymbolicExpression intArr2D_b;
	private SymbolicExpression intArr_c;
	private NumericExpression i;
	private NumericExpression j;
	private NumericExpression k;
	private NumericExpression m;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		zero = universe.integer(0);
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		six = universe.integer(6);
		integerType = universe.integerType();
		arrayType2D = universe.arrayType(universe.arrayType(integerType));
		arrayType = universe.arrayType(integerType);
		a_obj = universe.stringObject("a");
		b_obj = universe.stringObject("b");
		i_obj = universe.stringObject("i");
		j_obj = universe.stringObject("j");
		k_obj = universe.stringObject("k");
		m_obj = universe.stringObject("m");
		intArr_a = universe.symbolicConstant(
				a_obj, arrayType);
		intArr2D_b = universe.symbolicConstant(
				b_obj, arrayType2D);
		intArr_c = universe.symbolicConstant(
				a_obj, arrayType);
		i = (NumericExpression) universe
				.symbolicConstant(i_obj, integerType);
		j = (NumericExpression) universe
				.symbolicConstant(j_obj, integerType);
		k = (NumericExpression) universe
				.symbolicConstant(k_obj, integerType);
		m = (NumericExpression) universe
				.symbolicConstant(m_obj, integerType);
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void arrayAccessReason() {
		SymbolicExpression a2 = universe.arrayWrite(intArr_a, i, six);
		SymbolicExpression x = universe.arrayRead(a2, two);
		Reasoner r = universe.reasoner(universe.equals(i, two));
		out.println("x=" + x);

		assertEquals(six, r.simplify(x));
	}
	
	@Test
	public void array2DAccessReason(){
		SymbolicExpression row = universe.arrayRead(intArr2D_b, two);
		SymbolicExpression newRow = universe.arrayWrite(row, three, six);
		SymbolicExpression newArray2D = universe.arrayWrite(intArr2D_b, two, newRow);
		SymbolicExpression r1 = universe.arrayRead(newArray2D, i);
		SymbolicExpression r2 = universe.arrayRead(r1, j);
		
		Reasoner r = universe.reasoner(universe.and(universe.equals(i, two), universe.equals(j, three)));
		assertEquals(six, r.simplify(r2));
	}
	
	@Test
	public void arrayCompareReasonTest(){
		SymbolicExpression a1 = universe.arrayWrite(intArr_a, i, k);
		SymbolicExpression a2 = universe.arrayWrite(a1, j, m);
		NumericExpression r1 = (NumericExpression)universe.arrayRead(a2, i);
		NumericExpression r2 = (NumericExpression)universe.arrayRead(a2, j);
		
		Reasoner reasoner1 = universe.reasoner(universe.lessThan(k, m));
		BooleanExpression lessThan1 = universe.lessThan(r1, r2);
		ValidityResult result1 = reasoner1.valid(lessThan1);
		assertEquals(ResultType.NO, result1.getResultType());
		
		Reasoner reasoner2 = universe.reasoner(universe.and(universe.lessThan(k, m), universe.neq(i, j)));
		BooleanExpression lessThan2 = universe.lessThan(r1, r2);
		ValidityResult result2 = reasoner2.valid(lessThan2);
		assertEquals(ResultType.YES, result2.getResultType());
	}
	
	@Test
	public void arrayWriteReasonTest(){
		List<NumericExpression> values = new ArrayList<NumericExpression>();
		for(int i=0; i<5; i++){
			values.add(universe.add((NumericExpression)universe.arrayRead(intArr_a, universe.integer(i)), one));
		}
		SymbolicExpression a1 = universe.denseArrayWrite(intArr_c, values);
		NumericExpression v1 = (NumericExpression)universe.arrayRead(a1, i);
		NumericExpression v2 = (NumericExpression)universe.arrayRead(intArr_a, i);
		NumericExpression v1SubV2 = universe.subtract(v1, v2);
		Reasoner reasoner = universe.reasoner(universe.and(universe.lessThanEquals(zero, i),
				universe.lessThan(i, five)));
		
		BooleanExpression lessThan = universe.lessThan(v2, v1);
		BooleanExpression equals = universe.equals(one, v1SubV2);
		ValidityResult result1 = reasoner.valid(lessThan);
		ValidityResult result2 = reasoner.valid(equals);
		assertEquals(ResultType.YES, result1.getResultType());
		assertEquals(ResultType.YES, result2.getResultType());
	}
}
