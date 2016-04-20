package edu.udel.cis.vsl.civl.model.common.expression.reference;

import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.StructOrUnionFieldReference;

public class CommonStructOrUnionFieldReference extends CommonReference
		implements StructOrUnionFieldReference {

	/**
	 * The field index of this reference.
	 */
	private int fieldIndex;

	/**
	 * Creates a new instance of struct or union field reference.
	 * 
	 * @param fieldIndex
	 *            The field index of the reference.
	 * @param child
	 *            The child of the reference.
	 */
	public CommonStructOrUnionFieldReference(int fieldIndex,
			MemoryUnitReference child) {
		super(child);
		this.fieldIndex = fieldIndex;
	}

	/**
	 * Creates a new instance of struct or union field reference. Use null as
	 * the child.
	 * 
	 * @param fieldIndex
	 *            The field index of the reference.
	 */
	public CommonStructOrUnionFieldReference(int fieldIndex) {
		super(null);
		this.fieldIndex = fieldIndex;
	}

	@Override
	public MemoryUnitReferenceKind memoryUnitKind() {
		return MemoryUnitReferenceKind.STRUCT_OR_UNION_FIELD;
	}

	@Override
	public int fieldIndex() {
		return this.fieldIndex;
	}

	@Override
	protected boolean equalsReference(MemoryUnitReference ref) {
		StructOrUnionFieldReference that = (StructOrUnionFieldReference) ref;

		if (this.fieldIndex == that.fieldIndex())
			return this.childEquals(that);
		return false;
	}

	@Override
	protected StringBuffer toStringBuffer() {
		StringBuffer result = new StringBuffer();

		result.append(".");
		result.append(fieldIndex);
		if (child != null)
			result.append(child.toString());
		return result;
	}
}
