package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.value.IF.CastValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public class CommonCastValue extends CommonValue implements CastValue {

	private final static int classCode = CommonCastValue.class.hashCode();

	private Value argument;

	public CommonCastValue(Type type, Value argument) {
		super(type);
		assert argument != null;
		this.argument = argument;
	}

	@Override
	public Type getCastType() {
		return getType();
	}

	@Override
	public Value getArgument() {
		return argument;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonCastValue) {
			CommonCastValue that = (CommonCastValue) object;

			return getType().equals(that.getType())
					&& argument.equals(that.argument);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + argument.hashCode();
	}

	@Override
	public Answer isZero() {
		return argument.isZero();
	}

	@Override
	public String toString() {
		return "(" + getCastType() + ")" + argument;
	}

}
