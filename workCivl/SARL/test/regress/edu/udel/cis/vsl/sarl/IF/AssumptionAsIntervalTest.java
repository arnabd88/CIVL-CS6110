package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertTrue;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class AssumptionAsIntervalTest {
	private SymbolicUniverse universe = SARL.newStandardUniverse();
	private SymbolicType intType = universe.integerType();
	private NumericExpression one = universe.integer(1);
	private NumericExpression two = universe.integer(2);

	// Context: (X0+-2 <= 0) && (X1+-2 <= 0) && (0 <= X0+-1) && (0 <= X1+-1)
	// expected interval of X0, X1: [1, 2]
	// THIS TEST MISCONSTRUES THE CONTRACT FOR assumptionAsInterval.
	// However a new method should be added to do what this test asks.
	// Then this test can be fixed and used.
	@Ignore
	@Test
	public void getInterval() {
		NumericExpression X0 = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("X0"), intType);
		NumericExpression X1 = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("X1"), intType);
		BooleanExpression context;
		Reasoner reasoner;
		Interval intervalX0, intervalX1;

		context = universe.lessThanEquals(X0, two);
		context = universe.and(context, universe.lessThanEquals(X1, two));
		context = universe.and(context, universe.lessThanEquals(one, X0));
		context = universe.and(context, universe.lessThanEquals(one, X1));
		System.out.println("context: " + context);
		reasoner = universe.reasoner(context);
		intervalX0 = reasoner.assumptionAsInterval((SymbolicConstant) X0);
		intervalX1 = reasoner.assumptionAsInterval((SymbolicConstant) X1);
		System.out.println("interval of X0: " + intervalX0);
		System.out.println("interval of X1: " + intervalX1);
		assertTrue(intervalX0 != null);
		assertTrue(intervalX1 != null);
	}
}
