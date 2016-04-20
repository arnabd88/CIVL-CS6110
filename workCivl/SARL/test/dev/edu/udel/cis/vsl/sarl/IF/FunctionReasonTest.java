package edu.udel.cis.vsl.sarl.IF;

import java.util.Arrays;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;

public class FunctionReasonTest {
	private SymbolicUniverse universe;
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
	}
	
	@After
	public void tearDown() throws Exception {
	}
	
	@Test
	public void reasonerTest() {
		ReferenceExpression self = universe.identityReference();
		ReferenceExpression arrayEle1 = universe.arrayElementReference(self,
				universe.integer(1));
		Reasoner reasoner = universe.reasoner(universe.trueExpression());
		SymbolicFunctionType functionType = universe
				.functionType(Arrays.asList(universe.referenceType()),
						universe.booleanType());
		SymbolicConstant function = universe.symbolicConstant(
				universe.stringObject("function"), functionType);
		BooleanExpression claim = (BooleanExpression) universe.apply(function,
				Arrays.asList(arrayEle1));
		reasoner.isValid(claim);
	}
	
}
