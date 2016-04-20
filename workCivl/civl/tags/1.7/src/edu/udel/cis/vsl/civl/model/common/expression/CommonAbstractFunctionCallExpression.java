package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.AbstractFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * This implements an abstract function call expression.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonAbstractFunctionCallExpression extends CommonExpression
		implements AbstractFunctionCallExpression {

	/* ************************** Private Fields *************************** */

	/**
	 * The abstract function that this call expression invokes.
	 */
	private AbstractFunction function;

	/**
	 * The list of arguments of this call expression.
	 */
	private List<Expression> arguments;

	/* **************************** Constructor **************************** */

	/**
	 * Creates a new instance of an abstract function call.
	 * 
	 * @param source
	 *            The source information corresponding to this abstract function
	 *            call.
	 * @param scope
	 *            The highest scope that this function call accessed through its
	 *            arguments.
	 * @param function
	 *            The abstract function.
	 * @param arguments
	 *            Expressions for the arguments used in the abstract function
	 *            call.
	 */
	public CommonAbstractFunctionCallExpression(CIVLSource source,
			Scope hscope, Scope lscope, AbstractFunction function,
			List<Expression> arguments) {
		super(source, hscope, lscope, function.returnType());
		this.function = function;
		this.arguments = arguments;
	}

	/* ********************** Methods from Expression ********************** */

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ABSTRACT_FUNCTION_CALL;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return null;
	}

	/* ************* Methods from AbstractFunctionCallExpression *********** */

	@Override
	public AbstractFunction function() {
		return function;
	}

	@Override
	public List<Expression> arguments() {
		return arguments;
	}

	/* ************************ Methods from Object ************************ */

	@Override
	public String toString() {
		String result = function.name().name() + "(";

		for (int i = 0; i < arguments.size(); i++) {
			if (i != 0) {
				result += ", ";
			}
			result += arguments.get(i);
		}
		result += ")";
		return result;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		AbstractFunctionCallExpression that = (AbstractFunctionCallExpression) expression;

		if (this.function.name().name().equals(that.function().name().name())) {
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
