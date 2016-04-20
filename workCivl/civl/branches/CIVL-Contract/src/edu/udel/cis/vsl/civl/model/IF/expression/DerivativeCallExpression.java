package edu.udel.cis.vsl.civl.model.IF.expression;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.util.IF.Pair;

/**
 * An uninterpreted call to the derivative of an abstract function.
 * 
 * @author zirkel
 * 
 */
public interface DerivativeCallExpression extends
		AbstractFunctionCallExpression {

	/**
	 * @return The list of pairs of partial derivatives taken. Each pair has the
	 *         variable that is the parameter for which the partial derivative
	 *         is taken, and number of times that partial derivative is taken.
	 */
	List<Pair<Variable, IntegerLiteralExpression>> partials();

}
