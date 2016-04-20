/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.math.BigDecimal;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A real literal.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonRealLiteralExpression extends CommonExpression implements
		RealLiteralExpression {

	private BigDecimal value;

	/**
	 * A real literal.
	 * 
	 * @param value
	 *            The (arbitrary precision) real value.
	 */
	public CommonRealLiteralExpression(CIVLSource source, CIVLType type,
			BigDecimal value) {
		super(source, null, null, type);
		this.value = value;
	}

	/**
	 * @return The (arbitrary precision) real value.
	 */
	public BigDecimal value() {
		return value;
	}

	/**
	 * @param value
	 *            The (arbitrary precision) real value.
	 */
	public void setValue(BigDecimal value) {
		this.value = value;
	}

	@Override
	public String toString() {
		return value.toString();
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.REAL_LITERAL;
	}

	@Override
	public CIVLPrimitiveType getExpressionType() {
		return (CIVLPrimitiveType) super.getExpressionType();
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return null;
	}

	@Override
	public LiteralKind literalKind() {
		return LiteralKind.REAL;
	}

	@Override
	public void calculateConstantValueWork(SymbolicUniverse universe) {
		this.constantValue = universe.number(universe.numberObject(universe
				.numberFactory().rational(value.toPlainString())));
	}

	@Override
	public void setLiteralConstantValue(SymbolicExpression value) {
		this.constantValue = value;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		return this.value == ((RealLiteralExpression) expression).value();
	}
}
