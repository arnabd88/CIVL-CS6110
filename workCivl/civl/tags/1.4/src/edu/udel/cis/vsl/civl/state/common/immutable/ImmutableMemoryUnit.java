package edu.udel.cis.vsl.civl.state.common.immutable;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.state.IF.MemoryUnit;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;

public class ImmutableMemoryUnit implements MemoryUnit {

	/* ************************** Instance Fields ************************** */

	/**
	 * The ID of the dyscope that this memory unit belongs to.
	 */
	private int dyscopeID;

	/**
	 * The ID of the variable that this memory unit corresponds to.
	 */
	private int varID;

	/**
	 * The reference that describes how this memory unit relates to the
	 * corresponding variable, e.g., array element, tuple component, identity,
	 * etc.
	 */
	private ReferenceExpression reference;

	/**
	 * Is this instance the canonic representative of its equivalence class
	 * under the "equals" method?
	 */
	private boolean canonic = false;

	/**
	 * If the hash code has been computed, it is cached here.
	 */
	private int hashCode = -1;

	/**
	 * Has the hash code been computed?
	 */
	private boolean hashed = false;

	/* **************************** Constructor **************************** */

	/**
	 * Creates a new instance of memory unit.
	 * 
	 * @param dyscopeID
	 *            The ID of the dyscope that the new memory unit belongs to.
	 * @param varID
	 *            The ID of the variable that the new memory unit corresponds
	 *            to.
	 * @param reference
	 *            The reference that shows how the new memory unit relates to
	 *            the corresponding variable.
	 */
	ImmutableMemoryUnit(int dyscopeID, int varID, ReferenceExpression reference) {
		this.dyscopeID = dyscopeID;
		this.varID = varID;
		this.reference = reference;
	}

	/* ********************** Package-private Methods ********************** */
	/**
	 * Makes this instance the canonic representative of its equivalence class
	 * under "equals". Makes all the variable values canonic as well.
	 * 
	 * @param universe
	 *            the symbolic universe that is used to make the variable values
	 *            canonic
	 */
	void makeCanonic(SymbolicUniverse universe) {
		assert !canonic;
		canonic = true;
		universe.canonic(this.reference);
	}

	/**
	 * Is this instance the unique representative of its equivalence class?
	 * 
	 * @return true iff this is the canonic representative of its equivalence
	 *         class
	 */
	boolean isCanonic() {
		return this.canonic;
	}

	/* ********************** Methods from MemoryUnit ********************** */

	@Override
	public int dyscopeID() {
		return this.dyscopeID;
	}

	@Override
	public int varID() {
		return this.varID;
	}

	@Override
	public ReferenceExpression reference() {
		return this.reference;
	}

	/* ************************ Methods from Object ************************ */

	@Override
	public String toString() {
		return "(" + dyscopeID + ", " + varID + ", " + reference + ")";
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof ImmutableMemoryUnit) {
			ImmutableMemoryUnit that = (ImmutableMemoryUnit) obj;

			if (this.canonic && that.canonic)
				return false;
			if (this.dyscopeID != that.dyscopeID)
				return false;
			if (this.varID != that.varID)
				return false;
			return this.reference.equals(that.reference);
		}
		return false;
	}

	@Override
	public int hashCode() {
		if (!hashed) {
			hashCode = dyscopeID ^ (31 * varID) ^ reference.hashCode();
		}
		return hashCode;
	}

	@Override
	public void print(PrintStream out) {
		out.print(toString());
	}

}
