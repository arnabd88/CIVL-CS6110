package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A system guard expression stores the necessary information (library, function
 * name and arguments of the function call) for calculating the guard of a
 * system function call.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonSystemGuardExpression extends CommonExpression implements
		SystemGuardExpression {

	/* *************************** Instance Fields ************************* */

	/**
	 * The library that the invoked function belongs to.
	 */
	private String library;

	/**
	 * The name of the invoked function.
	 */
	private String functionName;

	/**
	 * The list of arguments that the function call uses.
	 */
	private List<Expression> arguments;

	/* **************************** Constructors *************************** */

	/**
	 * Create a new instance of system guard expression.
	 * 
	 * @param source
	 *            The source code element to be used for error report.
	 * @param library
	 *            The name of the library that the invoked function belongs to.
	 * @param function
	 *            The name of the invoked function.
	 * @param args
	 *            The list of arguments used in the function call.
	 * @param type
	 *            The type of this expression (should be always boolean type).
	 */
	public CommonSystemGuardExpression(CIVLSource source, Scope scope,
			String library, String function, List<Expression> args,
			CIVLType type) {
		super(source, scope, scope, type);
		this.library = library;
		this.functionName = function;
		this.arguments = args;
	}

	/* *********************** Methods from Expression ********************* */

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.SYSTEM_GUARD;
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

	/* ***************** Methods from SystemGuardExpression *************** */

	@Override
	public String library() {
		return this.library;
	}

	@Override
	public String functionName() {
		return this.functionName;
	}

	@Override
	public List<Expression> arguments() {
		return this.arguments;
	}

	/* *********************** Methods from Object ********************* */
	@Override
	public String toString() {
		return "guard[" + this.library + "." + this.functionName + "()]";
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		// TODO Auto-generated method stub
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
