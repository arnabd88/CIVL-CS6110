package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;

/**
 * When translating an $atom block, we need to create a noop statement at the
 * beginning and at the end of the block. In order to have more information
 * about the transitions, we create this class to extend
 * {@link CommonNoopStatement}. Currently, there is a field {@link #enter} to
 * denote if the statement is
 * <ol>
 * <li>entering an $atom block; or</li>
 * <li>leaving an $atom block.</li>
 * </ol>
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonAtomBranchStatement extends CommonNoopStatement {

	/* *************************** Instance Fields ************************* */

	/**
	 * Denote if this statement is
	 * <ol>
	 * <li>enter == true: entering an $atom block; or</li>
	 * <li>enter == false: leaving an $atom block.</li>
	 * </ol>
	 */
	private boolean enter;

	/* **************************** Constructors *************************** */

	/**
	 * 
	 * @param civlSource
	 *            The CIVL source of this statement. More information in
	 *            {@link CIVLSource}.
	 * @param source
	 *            The source location of this goto statement
	 * @param atomicKind
	 *            The atomic kind of this statement
	 */
	public CommonAtomBranchStatement(CIVLSource civlSource, Location source,
			Expression guard, boolean isEntering) {
		super(civlSource, source, guard, null);
		this.noopKind = NoopKind.ATOMIC_ATOM;
		this.enter = isEntering;
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		if (enter)
			return "ENTER_ATOM";
		return "LEAVE_ATOM";
	}

}
