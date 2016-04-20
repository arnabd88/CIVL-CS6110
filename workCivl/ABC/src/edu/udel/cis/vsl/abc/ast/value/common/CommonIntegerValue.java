package edu.udel.cis.vsl.abc.ast.value.common;

import java.math.BigInteger;

import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public class CommonIntegerValue extends CommonValue implements IntegerValue {

	private final static int classCode = CommonIntegerValue.class.hashCode();

	private BigInteger integerValue;

	public CommonIntegerValue(IntegerType type, BigInteger integerValue) {
		super(type);
		assert integerValue != null;
		this.integerValue = integerValue;
	}

	@Override
	public BigInteger getIntegerValue() {
		return integerValue;
	}

	@Override
	public IntegerType getType() {
		return (IntegerType) super.getType();
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonIntegerValue) {
			CommonIntegerValue that = (CommonIntegerValue) object;

			return getType().equals(that.getType())
					&& integerValue.equals(that.integerValue);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + integerValue.hashCode();
	}

	@Override
	public Answer isZero() {
		return integerValue.signum() == 0 ? Answer.YES : Answer.NO;
	}

	@Override
	public String toString() {
		return integerValue.toString();
	}

}
