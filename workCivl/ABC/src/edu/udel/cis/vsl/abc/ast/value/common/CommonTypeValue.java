package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.value.IF.TypeValue;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public class CommonTypeValue extends CommonValue implements TypeValue {

	private final static int classCode = CommonTypeValue.class.hashCode();

	private Type typeArgument;

	private TypeValueKind kind;

	public CommonTypeValue(IntegerType type, TypeValueKind kind,
			Type typeArgument) {
		super(type);
		assert typeArgument != null;
		this.typeArgument = typeArgument;
		this.kind = kind;
	}

	@Override
	public Type getTypeArgument() {
		return typeArgument;
	}

	@Override
	public IntegerType getType() {
		return (IntegerType) super.getType();
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonTypeValue) {
			CommonTypeValue that = (CommonTypeValue) object;

			return getType().equals(that.getType())
					&& typeArgument.equals(that.typeArgument);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + typeArgument.hashCode();
	}

	@Override
	public TypeValueKind getTypeValueKind() {
		return kind;
	}

	@Override
	public Answer isZero() {
		return Answer.NO;
	}

	@Override
	public String toString() {
		return kind + "[" + typeArgument + "]";
	}
}
