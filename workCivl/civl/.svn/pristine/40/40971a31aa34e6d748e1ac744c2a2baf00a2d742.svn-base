package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;

/**
 * When translating a switch block, we need to create a noop statement for each
 * label. In order to have more information about the transition, we create this
 * class to extend {@link CommonNoopStatement}. Currently, the label of the noop
 * statement is included as a field. In the future, we may put more information,
 * if necessary.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonSwitchBranchStatement extends CommonNoopStatement {

	/* *************************** Instance Fields ************************* */

	/**
	 * The corresponding label in the switch block for this noop statements.
	 */
	private Expression label;

	/* **************************** Constructors *************************** */

	/**
	 * Basic constructor. Every parameter should be non-null. If there is no
	 * label, use {@link #CommonSwitchBranchStatement(CIVLSource, Location)}
	 * 
	 * @param civlSource
	 * @param source
	 * @param label
	 */
	public CommonSwitchBranchStatement(CIVLSource civlSource, Location source,
			Expression label) {
		super(civlSource, source);
		this.noopKind = NoopKind.SWITCH;
		this.label = label;
	}

	/**
	 * Create a noop statement for the default case of a switch block. Each
	 * parameter should be non-null. For cases other than default, use
	 * {@link #CommonSwitchBranchStatement(CIVLSource, Location, Expression)}
	 * 
	 * @param civlSource
	 * @param source
	 */
	public CommonSwitchBranchStatement(CIVLSource civlSource, Location source) {
		super(civlSource, source);
		this.noopKind = NoopKind.SWITCH;
		this.label = null;
	}

	/* ************************ Methods from Object ************************ */

	@Override
	public String toString() {
		if (label == null)
			return "DEFAULT";
		else {
			return "CASE_" + label.toString();
		}
	}
}
