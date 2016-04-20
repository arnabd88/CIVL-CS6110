/**
 * 
 */
package edu.udel.cis.vsl.civl.transition;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A choose transition represents one of the outgoing transitions from a choose
 * statement. There is one such transition for each value that can result from
 * the choose.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class ChooseTransition extends SimpleTransition {

	private SymbolicExpression value;

	/**
	 * A choose transition represents one of the outgoing transitions from a
	 * choose statement. There is one such transition for each value that can
	 * result from the choose.
	 * 
	 * @param pathCondition
	 *            The path condition that should be used when executing this
	 *            transition
	 * @param pid
	 *            The process id of the process executing this transition.
	 * @param processIdentifier
	 *            The process identifier of the process executing this
	 *            transition.
	 * @param statement
	 *            The statement corresponding to this transition.
	 * @param value
	 *            The value resulting from the choose for this transition.
	 */
	public ChooseTransition(BooleanExpression pathCondition, int pid,
			int processIdentifier, Statement statement, SymbolicExpression value) {
		super(pathCondition, pid, processIdentifier, statement);
		this.value = value;
	}

	/**
	 * The value resulting from the choose for this transition.
	 */
	public SymbolicExpression value() {
		return value;
	}

	@Override
	public String toString() {
		CIVLSource source = statement.getSource();
		String result = super.toString() + " (" + value + ")";

		if (source != null)
			result += " at " + source.getSummary();
		return result;
	}
}
