package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.LoopBranchStatement;

public class CommonLoopBranchStatement extends CommonNoopStatement implements
		LoopBranchStatement {

	/* *************************** Instance Fields ************************* */

	/**
	 * Mark this statement to be the if branch or else branch.
	 */
	private boolean isTrueBranch;

	/* ************************** Instance Fields ************************** */

	/**
	 * 
	 * @param civlSource
	 *            The CIVL source of this statement
	 * @param source
	 *            The source location of this statement
	 * @param isTrue
	 *            true iff this is the if branching, else the else branching.
	 */
	public CommonLoopBranchStatement(CIVLSource civlSource, Location source,
			Expression guard, boolean isTrue) {
		super(civlSource, source, guard, null);
		this.noopKind = NoopKind.LOOP;
		this.isTrueBranch = isTrue;
		this.statementScope = guard.expressionScope();
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		if (isTrueBranch) {
			return "LOOP_BODY_ENTER";
		} else
			return "LOOP_BODY_EXIT";
	}

	@Override
	public boolean isEnter() {
		return this.isTrueBranch;
	}
}
