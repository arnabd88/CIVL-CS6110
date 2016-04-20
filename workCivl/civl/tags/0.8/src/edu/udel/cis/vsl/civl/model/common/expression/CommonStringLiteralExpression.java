/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A string literal.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonStringLiteralExpression extends CommonExpression implements
		StringLiteralExpression {

	private String value;

	/**
	 * A string literal.
	 * 
	 * @param value
	 *            The string.
	 */
	public CommonStringLiteralExpression(CIVLSource source, String value) {
		super(source);
		this.value = value;
	}

	/**
	 * @return The string.
	 */
	public String value() {
		return value;
	}

	/**
	 * @param value
	 *            The string.
	 */
	public void setValue(String value) {
		this.value = value;
	}

	@Override
	public String toString() {
		return value;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.STRING_LITERAL;
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
