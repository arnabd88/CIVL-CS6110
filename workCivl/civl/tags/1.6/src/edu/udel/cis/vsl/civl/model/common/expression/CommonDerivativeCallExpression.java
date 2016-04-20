package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.DerivativeCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.util.IF.Pair;

public class CommonDerivativeCallExpression extends
		CommonAbstractFunctionCallExpression implements
		DerivativeCallExpression {

	private List<Pair<Variable, IntegerLiteralExpression>> partials;

	/**
	 * An abstract function call.
	 * 
	 * @param source
	 *            The source information corresponding to this abstract function
	 *            call.
	 * @param function
	 *            The abstract function.
	 * @param partials
	 *            The pairs representing which partial derivatives are taken.
	 *            Each pair is comprised of the variable for the parameter in
	 *            which the partial derivative is taken, and an integer
	 *            indicating how many times that partial is taken.
	 * @param arguments
	 *            Expressions for the arguments used in the abstract function
	 *            call.
	 */
	public CommonDerivativeCallExpression(CIVLSource source, Scope hscope,
			Scope lscope, AbstractFunction function,
			List<Pair<Variable, IntegerLiteralExpression>> partials,
			List<Expression> arguments) {
		super(source, hscope, lscope, function, arguments);
		this.partials = partials;
	}

	@Override
	public List<Pair<Variable, IntegerLiteralExpression>> partials() {
		return partials;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DERIVATIVE;
	}

	@Override
	public String toString() {
		String result = "$D[" + function().name().name();

		for (Pair<Variable, IntegerLiteralExpression> partial : partials) {
			result += ", {";
			result += partial.left.name().name();
			result += ",";
			result += partial.right.value().toString();
			result += "}";
		}
		result += "](";
		for (int i = 0; i < arguments().size(); i++) {
			if (i != 0) {
				result += ", ";
			}
			result += arguments().get(i);
		}
		result += ")";
		return result;
	}

}
