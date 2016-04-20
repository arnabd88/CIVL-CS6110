package edu.udel.cis.vsl.abc.main;

import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * This example shows how to tell if two numeric expressions are equivalent.
 * 
 * @author siegel
 * 
 */
public class ProverExample {

	/**
	 * Create new ProverExample that will use the given symbolic universe. Note
	 * there is a symbolic universe in the {@link Activator}.
	 * 
	 * 
	 * @param universe
	 */
	public ProverExample(SymbolicUniverse universe) {
		// the context is the underlying assumption that will be used
		// when reasoning about validity. It is usually the "path condition"....
		BooleanExpression context = universe.trueExpression();
		// a reasoner for the specified context is used to check validity,
		// satisfiability, and to simplify expressions...
		Reasoner reasoner = universe.reasoner(context);
		SymbolicType integerType = universe.integerType();
		// a NumericSymbolicConstant is both a SymbolicConstant and a
		// NumericExpression;
		// a NumericExpression is a SymbolicExpression which has integer or real
		// type...
		NumericSymbolicConstant x1 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X1"), integerType);
		NumericSymbolicConstant x2 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X2"), integerType);
		// methods add, subtract, etc. require two NumericExpressions...
		NumericExpression e1 = universe.add(x1, x2);
		NumericExpression e2 = universe.subtract(x1, x2);
		BooleanExpression equiv = universe.equals(e1, e2);
		ValidityResult result = reasoner.valid(equiv);
		ResultType resultType = result.getResultType();

		// alternatively, you can use method reasoner.isValid()
		// if you just care about true/false (maybe maps to false)

		switch (resultType) {
		case MAYBE:
			System.out.println("Not sure");
			break;
		case NO:
			System.out.println("Not equivalent");
			break;
		case YES:
			System.out.println("Equivalent");
			break;
		default:
			// unreachable
			assert false;
		}

	}
}
