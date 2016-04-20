package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonFunctionGuardExpression extends CommonExpression implements
		FunctionGuardExpression {

	/**
	 * The expression of the function pointer of the corresponding function
	 * call.
	 */
	private Expression functionExpression;

	/**
	 * The arguments of the function call.
	 */
	private List<Expression> arguments;

	public CommonFunctionGuardExpression(CIVLSource source,
			Expression function, List<Expression> arguments, CIVLType type) {
		super(source, null, null, type);
		this.functionExpression = function;
		this.arguments = arguments;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.FUNCTION_GUARD;
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
	public Expression functionExpression() {
		return this.functionExpression;
	}

	@Override
	public List<Expression> arguments() {
		return this.arguments;
	}

	@Override
	public String toString() {
		return "guard[" + this.functionExpression + "()]";
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		FunctionGuardExpression that = (FunctionGuardExpression) expression;

		if (this.functionExpression.equals(that.functionExpression())) {
			int thisArgSize = this.arguments.size();

			if (thisArgSize == that.arguments().size()) {
				for (int i = 0; i < thisArgSize; i++)
					if (!this.arguments.get(i).equals(that.arguments().get(i)))
						return false;
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean containsHere() {
		for (Expression arg : arguments) {
			if (arg.containsHere())
				return true;
		}
		return false;
	}

}
