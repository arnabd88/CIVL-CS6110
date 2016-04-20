/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * Self expression. Returns a reference to the process in which the expression
 * is evaluated.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonSelfExpression extends CommonExpression implements
		SelfExpression {

	/**
	 * Self expression. Returns a reference to the process in which the
	 * expression is evaluated.
	 */
	public CommonSelfExpression(CIVLSource source) {
		super(source);
	}

	@Override
	public String toString() {
		return "$self";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.SELF;
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
