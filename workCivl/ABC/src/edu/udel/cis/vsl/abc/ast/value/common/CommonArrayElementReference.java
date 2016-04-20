package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.value.IF.AddressValue;
import edu.udel.cis.vsl.abc.ast.value.IF.ArrayElementReference;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;

public class CommonArrayElementReference extends CommonAddressValue implements
		ArrayElementReference {

	private final static int classCode = CommonArrayElementReference.class
			.hashCode();

	private AddressValue arrayReference;

	private Value index;

	public CommonArrayElementReference(PointerType type,
			AddressValue arrayReference, Value index) {
		super(type);
		this.arrayReference = arrayReference;
		this.index = index;
	}

	@Override
	public Value getIndex() {
		return index;
	}

	@Override
	public AddressValue getArrayReference() {
		return arrayReference;
	}

	@Override
	public String toString() {
		return "ArrayElementReference[" + arrayReference + ", " + index + "]";
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonArrayElementReference) {
			CommonArrayElementReference that = (CommonArrayElementReference) object;

			return arrayReference.equals(that.arrayReference)
					&& index.equals(that.index);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + arrayReference.hashCode() + index.hashCode();
	}

}
