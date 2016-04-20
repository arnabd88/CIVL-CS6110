/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;

/**
 * A function call or spawn. Either of the form f(x) or else v=f(x).
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonCallStatement extends CommonStatement implements
		CallOrSpawnStatement {

	private boolean isCall;

	private LHSExpression lhs = null;

	private CIVLFunction function;

	private Vector<Expression> arguments;

	/**
	 * A function call. Either of the form f(x) or else v=f(x).
	 * 
	 * @param source
	 *            The source location for this call statement.
	 * @param isCall
	 *            is this a call statement (not fork)?
	 * @param function
	 *            The function.
	 * @param arguments
	 *            The arguments to the function.
	 */
	public CommonCallStatement(CIVLSource civlSource, Location source,
			boolean isCall, CIVLFunction function, Vector<Expression> arguments) {
		super(civlSource, source);
		this.isCall = isCall;
		this.function = function;
		this.arguments = arguments;
	}

	/**
	 * A function call.
	 * 
	 * @param source
	 *            The source location for this call statement.
	 * @param lhs
	 *            The (optional) left hand side expression. Used when the call
	 *            statement is also an assignment. Null if not applicable.
	 * @param function
	 *            The function.
	 * @param arguments
	 *            The arguments to the function.
	 */
	public CommonCallStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, CIVLFunction function, Vector<Expression> arguments) {
		super(civlSource, source);
		this.lhs = lhs;
		this.function = function;
		this.arguments = arguments;
	}

	/**
	 * @return The left hand side expression if applicable. Else null.
	 */
	@Override
	public LHSExpression lhs() {
		return lhs;
	}

	/**
	 * @return The function being called.
	 */
	@Override
	public CIVLFunction function() {
		return function;
	}

	/**
	 * @return The arguments to the function.
	 */
	@Override
	public Vector<Expression> arguments() {
		return arguments;
	}

	/**
	 * @param lhs
	 *            The left hand side expression if applicable. Else null.
	 */
	@Override
	public void setLhs(LHSExpression lhs) {
		this.lhs = lhs;
	}

	/**
	 * @param function
	 *            The function being called.
	 */
	@Override
	public void setFunction(CIVLFunction function) {
		this.function = function;
	}

	/**
	 * @param arguments
	 *            The arguments to the function.
	 */
	@Override
	public void setArguments(Vector<Expression> arguments) {
		this.arguments = arguments;
	}

	@Override
	public String toString() {
		String result = function.name().name();
		boolean first = true;

		result += "(";
		for (Expression arg : arguments) {
			if (first)
				first = false;
			else
				result += ", ";
			result += arg.toString();
		}
		result += ")";
		if (!isCall)
			result = "$spawn " + result;
		if (lhs != null) {
			result = lhs + " = " + result;
		}
		return result;
	}

	@Override
	public boolean isCall() {
		return isCall;
	}

	@Override
	public boolean isSpawn() {
		return !isCall;
	}

}
