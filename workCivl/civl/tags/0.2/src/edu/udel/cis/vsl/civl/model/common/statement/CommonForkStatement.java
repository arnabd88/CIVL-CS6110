/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.ForkStatement;

/**
 * A fork statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonForkStatement extends CommonStatement implements
		ForkStatement {

	private Expression lhs;
	private Expression function;
	private Vector<Expression> arguments;

	/**
	 * A fork statement.
	 * 
	 * @param source
	 *            The source location for this fork.
	 * @param lhs
	 *            Expression for place where the process reference will be
	 *            stored. Null if non-existent.
	 * @param function
	 *            An expression evaluating to a function.
	 * @param arguments
	 *            The arguments to the function.
	 */
	public CommonForkStatement(Location source, Expression lhs,
			Expression function, Vector<Expression> arguments) {
		super(source);
		this.lhs = lhs;
		this.function = function;
		this.arguments = arguments;
	}

	/**
	 * @return Expression for place where the process reference will be stored.
	 *         Null if non-existent.
	 */
	public Expression lhs() {
		return lhs;
	}

	/**
	 * @return The function that is started in the new process.
	 */
	public Expression function() {
		return function;
	}

	/**
	 * @return The arguments to the function.
	 */
	public Vector<Expression> arguments() {
		return arguments;
	}

	/**
	 * @param lhs
	 *            Expression for place where the process reference will be
	 *            stored. Null if non-existent.
	 */
	public void setLhs(Expression lhs) {
		this.lhs = lhs;
		statementScope = join(statementScope, lhs.expressionScope());
	}

	/**
	 * @param function
	 *            The function that is started in the new process.
	 */
	public void setFunction(Expression function) {
		this.function = function;
	}

	/**
	 * @param arguments
	 *            The arguments to the function.
	 */
	public void setArguments(Vector<Expression> arguments) {
		this.arguments = arguments;
	}

	@Override
	public String toString() {
		String result = "";

		if (lhs != null) {
			result += lhs + " = ";
		}
		result += "spawn " + function + "(";
		for (int i = 0; i < arguments.size(); i++) {
			if (i != 0) {
				result += ", ";
			}
			result += arguments.get(i);
		}
		result += ")";
		return result;
	}

}
