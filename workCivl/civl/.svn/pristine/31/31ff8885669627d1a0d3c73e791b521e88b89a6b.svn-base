/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics.common;

import edu.udel.cis.vsl.civl.model.IF.location.Location.AtomicKind;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

/**
 * A CIVL transition involves a single atomic statement in one process. It is to
 * be contrasted with a synchronous transition, which involves two statements
 * executing together in two different processes.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonTransition implements Transition {

	/* *************************** Instance Fields ************************* */

	/**
	 * The path condition of the new state after this transition is executed.
	 */
	private BooleanExpression pathCondition;

	/**
	 * The PID of the process that this transition belongs to.
	 */
	private int pid;

	/**
	 * The identifier of the process that this transition belongs to.
	 */
	private int processIdentifier;

	/**
	 * The statement that this transition is to execute, which should be atomic,
	 * deterministic, and enabled in the context of the path condition.
	 */
	private Statement statement;

	/* ***************************** Constructors ************************** */

	/**
	 * <p>
	 * Creates a new instance of a CIVL transition.
	 * </p>
	 * <p>
	 * Precondition: the statement is enabled in the context of the given path
	 * condition. There exists a state in the state space such that the process
	 * PID with the given identifier has the given atomic, deterministic
	 * statement enabled.
	 * </p>
	 * 
	 * @param pathCondition
	 *            The path condition of the new state after the transition being
	 *            executed.
	 * @param pid
	 *            The PID of the process that the transition belongs to.
	 * @param processIdentifier
	 *            The identifier of the process that the transition belongs to.
	 * @param statement
	 *            The statement of the transition.
	 */
	public CommonTransition(BooleanExpression pathCondition, int pid,
			int processIdentifier, Statement statement) {
		this.pathCondition = pathCondition;
		this.pid = pid;
		this.statement = statement;
		this.processIdentifier = processIdentifier;
	}

	/* *********************** Methods from Transition ********************* */

	public int pid() {
		return pid;
	}

	public Statement statement() {
		return statement;
	}

	public int processIdentifier() {
		return this.processIdentifier;
	}

	@Override
	public BooleanExpression pathCondition() {
		return this.pathCondition;
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		String result = "p" + processIdentifier + ": ";

		result += statement.toStepString(AtomicKind.NONE, pid, false);
		return result;
	}
}
