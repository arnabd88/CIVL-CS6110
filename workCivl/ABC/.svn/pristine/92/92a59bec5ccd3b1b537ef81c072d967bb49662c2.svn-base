package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.value.IF.StringValue;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral;

public class CommonStringValue extends CommonValue implements StringValue {

	private final static int classCode = CommonStringValue.class.hashCode();

	private StringLiteral literal;

	public CommonStringValue(ArrayType stringType, StringLiteral literal) {
		super(stringType);
		assert literal != null;
		this.literal = literal;
	}

	@Override
	public ArrayType getType() {
		return (ArrayType) super.getType();
	}

	@Override
	public boolean equals(Object object) {
		if (object == this)
			return true;
		if (object instanceof CommonStringValue) {
			CommonStringValue that = (CommonStringValue) object;

			return getType().equals(that.getType())
					&& literal.equals(that.literal);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + literal.hashCode();
	}

	@Override
	public StringLiteral getLiteral() {
		return literal;
	}

	@Override
	public Answer isZero() {
		throw new RuntimeException("Cannot ask if string is 0");
	}

	@Override
	public String toString() {
		return literal.toString();
	}
}
