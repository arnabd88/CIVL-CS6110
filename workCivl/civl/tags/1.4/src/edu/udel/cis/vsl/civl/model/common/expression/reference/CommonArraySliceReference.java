package edu.udel.cis.vsl.civl.model.common.expression.reference;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.ArraySliceReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference;

public class CommonArraySliceReference extends CommonReference implements
		ArraySliceReference {
	/**
	 * The kind of the array slice, which could be ELEMENT, WILDCARD, or RANGE.
	 */
	private ArraySliceKind arraySliceKind;

	/**
	 * The index expression of the array slice. This could be an integer, a
	 * wild-card expression or a range expression, depending on
	 * {@link #arraySliceKind}.
	 */
	private Expression indexExpression;

	/**
	 * Creates a new instance of array slice reference.
	 * 
	 * @param sliceKind
	 * @param index
	 * @param child
	 */
	public CommonArraySliceReference(ArraySliceKind sliceKind,
			Expression index, MemoryUnitReference child) {
		super(child);
		this.arraySliceKind = sliceKind;
		this.indexExpression = index;
	}

	/**
	 * Creates a new instance of array slice reference.
	 * 
	 * @param sliceKind
	 * @param index
	 */
	public CommonArraySliceReference(ArraySliceKind sliceKind, Expression index) {
		super(null);
		this.arraySliceKind = sliceKind;
		this.indexExpression = index;
	}

	@Override
	public ArraySliceKind sliceKind() {
		return this.arraySliceKind;
	}

	@Override
	public MemoryUnitReferenceKind memoryUnitKind() {
		return MemoryUnitReferenceKind.ARRAY_SLICE;
	}

	@Override
	public Expression index() {
		return this.indexExpression;
	}

	@Override
	protected boolean equalsReference(MemoryUnitReference ref) {
		ArraySliceReference that = (ArraySliceReference) ref;

		if (this.indexExpression.equals(that.index()))
			return this.childEquals(that);
		return false;
	}

	@Override
	protected StringBuffer toStringBuffer() {
		StringBuffer result = new StringBuffer();

		result.append("[");
		result.append(indexExpression);
		result.append("]");
		if (child != null)
			result.append(child.toString());
		return result;
	}

}
