package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.value.IF.UnionValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public class CommonUnionValue extends CommonValue implements UnionValue {

	private final static int classCode = CommonUnionValue.class.hashCode();

	private Field field;

	private Value memberValue;

	public CommonUnionValue(StructureOrUnionType unionType, Field field,
			Value memberValue) {
		super(unionType);
		assert unionType.isUnion();
		assert field != null;
		assert memberValue != null;
		this.field = field;
		this.memberValue = memberValue;
	}

	@Override
	public Field getField() {
		return field;
	}

	@Override
	public Value getMemberValue() {
		return memberValue;
	}

	@Override
	public StructureOrUnionType getType() {
		return (StructureOrUnionType) super.getType();
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonUnionValue) {
			CommonUnionValue that = (CommonUnionValue) object;

			return getType().equals(that.getType())
					&& field.equals(that.getField())
					&& memberValue.equals(that.memberValue);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + field.hashCode() + memberValue.hashCode();
	}

	@Override
	public boolean isScalar() {
		return memberValue.isScalar();
	}

	@Override
	public Answer isZero() {
		return memberValue.isZero();
	}

	@Override
	public String toString() {
		return field.getName() + ":" + memberValue;
	}

}
