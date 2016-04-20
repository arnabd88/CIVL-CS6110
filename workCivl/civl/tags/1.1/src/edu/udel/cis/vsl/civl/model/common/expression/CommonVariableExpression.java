/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A use of a variable in an expression.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonVariableExpression extends CommonExpression implements
		VariableExpression {

	Variable variable;

	/**
	 * A use of a variable in an expression.
	 * 
	 * @param variable
	 *            The variable.
	 */
	public CommonVariableExpression(CIVLSource source, Variable variable) {
		// Don't need to worry about the expression scope of constants.
		super(source, variable.isConst() ? null : variable.scope(), variable
				.scope(), variable.type());
		this.variable = variable;
	}

	/**
	 * @return The variable
	 */
	public Variable variable() {
		return variable;
	}

	/**
	 * @param variable
	 *            The variable.
	 */
	public void setVariable(Variable variable) {
		this.variable = variable;
	}

	@Override
	public String toString() {
		return variable.name().name();
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.VARIABLE;
	}

	@Override
	public void setPurelyLocal(boolean pl) {
		this.variable.setPurelyLocal(pl);
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		if (this.variable.type().isPointerType()
				|| this.variable.type().isHandleType())
			this.setPurelyLocal(false);
		else if (funcScope.isDescendantOf(this.variable.scope()))
			this.setPurelyLocal(false);

	}

	@Override
	public void purelyLocalAnalysis() {
		this.purelyLocal = this.variable.purelyLocal();
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
	public Variable variableWritten(Scope scope) {
		Scope vScope = variable.scope();

		if (variable.isConst() || variable.isInput())
			return null;
		if (scope.equals(vScope) || scope.isDescendantOf(vScope))
			return variable;
		return null;
	}

	@Override
	public Variable variableWritten() {
		if (variable.isConst() || variable.isInput())
			return null;
		return variable;
	}

	@Override
	public LHSExpressionKind lhsExpressionKind() {
		return LHSExpressionKind.VARIABLE;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		VariableExpression that = (VariableExpression) expression;

		return this.variable.equals(that.variable());
	}

}
