/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ResultExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * This expression is only used in an ensures clause of a function contract to
 * refer to the returned value.
 * 
 * @author zirkel
 * 
 */
public class CommonResultExpression extends CommonExpression implements
		ResultExpression {

	/**
	 * This expression is only used in an ensures clause of a function contract
	 * to refer to the returned value.
	 */
	public CommonResultExpression(CIVLSource source) {
		super(source, null, null);
	}

	public String toString() {
		return "$result";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.RESULT;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		// TODO Auto-generated method stub
		return null;
	}
}
