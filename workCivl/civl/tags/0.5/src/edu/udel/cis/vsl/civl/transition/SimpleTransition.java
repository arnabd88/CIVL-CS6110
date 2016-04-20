/**
 * 
 */
package edu.udel.cis.vsl.civl.transition;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

/**
 * A simple transition involves a single atomic statement in one process. It is
 * to be contrasted with a synchronous transition, which involves two statements
 * executing together in two different processes.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class SimpleTransition extends Transition {

	protected int pid;

	protected Statement statement;

	/**
	 * A simple transition involves a single atomic statement in one process. It
	 * is to be contrasted with a synchronous transition, which involves two
	 * statements executing together in two different processes.
	 * 
	 * @param pathCondition
	 *            The path condition that should be used when executing
	 *            statement
	 * @param pid
	 *            The process id of the process executing this transition.
	 * @param statement
	 *            The statement corresponding to this transition.
	 */
	public SimpleTransition(BooleanExpression pathCondition, int pid,
			Statement statement) {
		super(pathCondition);
		this.pid = pid;
		this.statement = statement;
	}

	/**
	 * @return The process id of the process executing this transition.
	 */
	public int pid() {
		return pid;
	}

	/**
	 * @return The statement corresponding to this transition.
	 */
	public Statement statement() {
		return statement;
	}

	/**
	 * @param pid
	 *            The process id of the process executing this transition.
	 */
	public void setPid(int pid) {
		this.pid = pid;
	}

	/**
	 * @param statement
	 *            The statement corresponding to this transition.
	 */
	public void setStatement(Statement statement) {
		this.statement = statement;
	}

	@Override
	public String toString() {
		CIVLSource source = statement.getSource();
		String result = "proc " + pid + ": \n";

		result += "  " + statement.source().id() + "->";
		if (statement.target() != null)
			result += statement.target().id() + ": ";
		else
			result += "RET: ";
		result += statement.toString();
		if (source != null)
			result += " at " + source.getSummary();
		else if (statement.source().getSource() != null)
			result += " at " + statement.source().getSource().getSummary();
		return result;
	}

}
