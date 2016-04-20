package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;

public class CommonLoopBranchStatement extends CommonNoopStatement {

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
			boolean isTrue) {
		super(civlSource, source);
		this.noopKind = NoopKind.LOOP;
		this.isTrueBranch = isTrue;
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		if (isTrueBranch) {
			return "LOOP_TRUE_BRANCH";
		} else
			return "LOOP_FALSE_BRANCH";
	}

}
