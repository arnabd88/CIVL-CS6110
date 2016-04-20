package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;

/**
 * A goto statement (e.g., <code>goto l1;</code>) is usually translated to a
 * noop statement because it has no side-effect. In order to have more
 * information about the transition, we create this class to extend
 * {@link CommonNoopStatement}. Currently, there is a field {@link #labelName}
 * to denote the label of the target location of this goto statement.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonGotoBranchStatement extends CommonNoopStatement {

	/* ************************** Instance Fields ************************** */

	/**
	 * The label of the target statement of this goto statement
	 */
	private String labelName;

	/* **************************** Constructors *************************** */

	/**
	 * 
	 * @param civlSource
	 *            The CIVL source of this statement. More information in {@link CIVLSource}.
	 * @param source
	 *            The source location of this goto statement
	 * @param label
	 *            The label name of this goto statement
	 */
	public CommonGotoBranchStatement(CIVLSource civlSource, Location source,
			String label) {
		super(civlSource, source);
		this.labelName = label;
		this.noopKind = NoopKind.GOTO;
	}

	/* ************************ Methods from Object ************************ */

	@Override
	public String toString() {
		return "GOTO_" + labelName;
	}

}
