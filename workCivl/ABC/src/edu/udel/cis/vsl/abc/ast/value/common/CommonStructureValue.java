package edu.udel.cis.vsl.abc.ast.value.common;

import java.util.Arrays;

import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.value.IF.StructureValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public class CommonStructureValue extends CommonValue implements StructureValue {

	private final static int classCode = CommonStructureValue.class.hashCode();

	private Value[] members;

	public CommonStructureValue(StructureOrUnionType type) {
		super(type);
		assert type.isStruct();
		assert type.isComplete();
		members = new Value[type.getNumFields()];
	}

	@Override
	public Value getMember(Field field) {
		return members[field.getMemberIndex()];
	}

	@Override
	public Value getMember(int fieldIndex) {
		return members[fieldIndex];
	}

	@Override
	public void setMember(Field field, Value memberValue) {
		members[field.getMemberIndex()] = memberValue;
	}

	@Override
	public void setMember(int index, Value memberValue) {
		members[index] = memberValue;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonStructureValue) {
			CommonStructureValue that = (CommonStructureValue) object;

			return getType().equals(that.getType())
					&& Arrays.equals(members, that.members);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + Arrays.hashCode(members);
	}

	@Override
	public StructureOrUnionType getType() {
		return (StructureOrUnionType) super.getType();
	}

	@Override
	public Answer isZero() {
		throw new RuntimeException("Cannot ask if structure is 0");
	}

	@Override
	public String toString() {
		return members.toString();
	}

}
