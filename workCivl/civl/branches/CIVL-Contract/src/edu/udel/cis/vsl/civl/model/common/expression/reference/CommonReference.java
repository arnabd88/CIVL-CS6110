package edu.udel.cis.vsl.civl.model.common.expression.reference;

import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference;

/**
 * This is the base class of memory unit reference.
 * 
 * @author Manchun Zheng
 *
 */
public abstract class CommonReference implements MemoryUnitReference {
	/**
	 * The child of this reference. (in order to support recursive references)
	 */
	protected MemoryUnitReference child;

	/**
	 * Creates a new instance of common reference.
	 * 
	 * @param child
	 *            The child reference.
	 */
	protected CommonReference(MemoryUnitReference child) {
		this.child = child;
	}

	/**
	 * Checks if the given reference equals this one.
	 * <p>
	 * Precondition: the result of the method
	 * {@link MemoryUnitReference#memoryUnitKind()} of the given reference and
	 * this should be the same.
	 * 
	 * @param ref
	 *            The reference to be compared for equality with this.
	 * @return true iff the given reference equals this.
	 */
	protected abstract boolean equalsReference(MemoryUnitReference ref);

	protected abstract StringBuffer toStringBuffer();

	@Override
	public String toString() {
		return toStringBuffer().toString();
	}

	/**
	 * Checks if the child of the given reference equals the child of this.
	 * 
	 * @param that
	 *            The reference whose child is to be compared with the child of
	 *            this.
	 * @return true iff if the child of the given reference equals the child of
	 *         this.
	 */
	protected boolean childEquals(MemoryUnitReference that) {
		if ((this.child() != null) == (that.child() != null))
			if (this.child == null)
				return true;
			else
				return child.equals(that.child());
		return false;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof MemoryUnitReference) {
			MemoryUnitReference that = (MemoryUnitReference) obj;

			if (this.memoryUnitKind() == that.memoryUnitKind())
				return equalsReference(that);
		}
		return false;
	}

	@Override
	public MemoryUnitReference child() {
		return this.child;
	}

}
