package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation.AtomicKind;

/**
 * When translating an $atomic/$atom block, we need to create a noop statement
 * at the beginning and at the end of the block. In order to have more
 * information about the transitions, we create this class to extend
 * {@link CommonNoopStatement}. Currently, there is a field {@link #atomicKind}
 * to denote if the statement is
 * <ol>
 * <li>entering an $atomic/$atom block; or</li>
 * <li>leaving an $atomic/$atom block.</li>
 * </ol>
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonAtomicBranchStatement extends CommonNoopStatement {

	/************************** Instance Fields *************************/

	/**
	 * Denote if this statement is
	 * <ol>
	 * <li>entering an $atomic/$atom block; or</li>
	 * <li>leaving an $atomic/$atom block.</li>
	 * </ol>
	 */
	private AtomicKind atomicKind;

	/************************** Constructors *************************/

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
	public CommonAtomicBranchStatement(CIVLSource civlSource, Location source,
			AtomicKind atomicKind) {
		super(civlSource, source);
		this.noopKind = NoopKind.ATOMIC_ATOM;
		this.atomicKind = atomicKind;
	}

	/************************** Methods from Object *************************/

	@Override
	public String toString() {
		switch (this.atomicKind) {
		case ATOMIC_ENTER:
			return "ENTER_ATOMIC";
		case ATOMIC_EXIT:
			return "LEAVE_ATOMIC";
		case ATOM_ENTER:
			return "ENTER_ATOM";
		case ATOM_EXIT:
			return "LEAVE_ATOM";
		default:
			throw new CIVLInternalException("Unreachable", this.getSource());
		}
	}

}
