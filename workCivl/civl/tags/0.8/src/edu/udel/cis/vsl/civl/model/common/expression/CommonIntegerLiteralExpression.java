/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.math.BigInteger;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * An integer literal.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonIntegerLiteralExpression extends CommonExpression implements
		IntegerLiteralExpression {

	private BigInteger value;

	/**
	 * An integer literal.
	 * 
	 * @param value
	 *            The (arbitrary precision) value of the integer.
	 */
	public CommonIntegerLiteralExpression(CIVLSource source, BigInteger value) {
		super(source);
		this.value = value;
	}

	/**
	 * @return The (arbitrary precision) value of the integer.
	 */
	public BigInteger value() {
		return value;
	}

	/**
	 * @param value
	 *            The (arbitrary precision) value of the integer.
	 */
	public void setValue(BigInteger value) {
		this.value = value;
	}

	@Override
	public String toString() {
		return value.toString();
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.INTEGER_LITERAL;
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
