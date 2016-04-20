package edu.udel.cis.vsl.civl.model.common.expression.reference;

import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.SelfReference;

public class CommonSelfReference extends CommonReference implements
		SelfReference {

	/**
	 * Creates a new instance of self reference.
	 * 
	 * @param child
	 *            The child of this.
	 */
	public CommonSelfReference(MemoryUnitReference child) {
		super(child);
	}

	/**
	 * Creates a new instance of self reference. Use null as the child.
	 */
	public CommonSelfReference() {
		super(null);
	}

	@Override
	public MemoryUnitReferenceKind memoryUnitKind() {
		return MemoryUnitReferenceKind.SELF;
	}

	@Override
	protected boolean equalsReference(MemoryUnitReference ref) {
		return true;
	}

	@Override
	protected StringBuffer toStringBuffer() {
		StringBuffer result = new StringBuffer();

		result.append("self");
		if (child != null)
			result.append(child.toString());
		return result;
	}

}
