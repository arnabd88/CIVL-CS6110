package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.WaitGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A wait guard expression stores the expression of the joined process for
 * calculating the actual guard.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonWaitGuardExpression extends CommonExpression implements
		WaitGuardExpression {

	/* *************************** Instance Fields ************************* */

	/**
	 * The process that this wait statement is waiting for.
	 */
	private Expression joinedProcess;

	/* **************************** Constructors *************************** */

	/**
	 * Create a new instance of wait guard expression.
	 * 
	 * @param source
	 *            The source code element to be used for error report.
	 * @param process
	 *            The process that the wait statement waits for.
	 * @param type
	 *            The type of this expression (should be always boolean type).
	 */
	public CommonWaitGuardExpression(CIVLSource source, Expression process,
			CIVLType type) {
		super(source);
		this.joinedProcess = process;
		this.expressionType = type;
	}

	/* *********************** Methods from Expression ********************* */

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.WAIT_GUARD;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return null;
	}

	/* ****************** Methods from WaitGuardExpression ***************** */

	@Override
	public Expression joinedProcess() {
		return this.joinedProcess;
	}

	/* *********************** Methods from Object ********************* */

	@Override
	public String toString() {
		return "guard[" + this.joinedProcess + " terminated]";
	}
}
