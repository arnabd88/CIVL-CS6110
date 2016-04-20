package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.value.IF.AddressValue;
import edu.udel.cis.vsl.abc.ast.value.IF.MemberReference;

public class CommonMemberReference extends CommonAddressValue implements
		MemberReference {

	private final static int classCode = CommonMemberReference.class.hashCode();

	private AddressValue structureOrUnionReference;

	private Field field;

	public CommonMemberReference(PointerType type,
			AddressValue structureOrUnionReference, Field field) {
		super(type);
		this.structureOrUnionReference = structureOrUnionReference;
		this.field = field;
	}

	@Override
	public String toString() {
		return "MemberReference[" + structureOrUnionReference + ", " + field
				+ "]";
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonMemberReference) {
			CommonMemberReference that = (CommonMemberReference) object;

			return structureOrUnionReference
					.equals(that.structureOrUnionReference)
					&& field.equals(that.field);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + structureOrUnionReference.hashCode()
				+ field.hashCode();
	}

	@Override
	public Field getField() {
		return field;
	}

	@Override
	public AddressValue getStructureOrUnionReference() {
		return structureOrUnionReference;
	}

}
