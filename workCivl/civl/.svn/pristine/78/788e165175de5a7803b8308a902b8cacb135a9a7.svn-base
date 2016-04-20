package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.AbstractFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

public class CommonAbstractFunctionCallExpression extends CommonExpression
		implements AbstractFunctionCallExpression {

	private AbstractFunction function;

	private List<Expression> arguments;

	/**
	 * An abstract function call.
	 * 
	 * @param source
	 *            The source information corresponding to this abstract function
	 *            call.
	 * @param function
	 *            The abstract function.
	 * @param arguments
	 *            Expressions for the arguments used in the abstract function
	 *            call.
	 */
	public CommonAbstractFunctionCallExpression(CIVLSource source,
			AbstractFunction function, List<Expression> arguments) {
		super(source);
		this.function = function;
		this.arguments = arguments;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ABSTRACT_FUNCTION_CALL;
	}

	@Override
	public AbstractFunction function() {
		return function;
	}

	@Override
	public List<Expression> arguments() {
		return arguments;
	}
	
	@Override
	public String toString() {
		String result = function.name().name() + "(";
		
		for (int i = 0; i < arguments.size(); i++) {
			if (i!=0) {
				result += ", ";
			}
			result += arguments.get(i);
		}
		result += ")";
		return result;
	}

}
