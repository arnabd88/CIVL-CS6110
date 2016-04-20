package edu.udel.cis.vsl.abc.ast.value.common;

import java.util.ArrayList;

import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.value.IF.ArrayValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public class CommonArrayValue extends CommonValue implements ArrayValue {

	private final static int classCode = CommonArrayValue.class.hashCode();

	private ArrayList<Value> elements = new ArrayList<Value>();

	public CommonArrayValue(ArrayType type) {
		super(type);
	}

	@Override
	public Value getElement(int index) {
		if (index < elements.size())
			return null;
		else
			return elements.get(index);
	}

	@Override
	public void setElement(int index, Value elementValue) {
		int size = elements.size();

		if (index >= size) {
			for (int i = size; i <= index; i++)
				elements.add(null);
		}
		elements.set(index, elementValue);
	}

	@Override
	public ArrayType getType() {
		return (ArrayType) super.getType();
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonArrayValue) {
			CommonArrayValue that = (CommonArrayValue) object;

			return getType().equals(that.getType())
					&& elements.equals(that.elements);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + elements.hashCode();
	}

	@Override
	public Answer isZero() {
		throw new RuntimeException("Cannot ask if an array is zero");
	}

	@Override
	public String toString() {
		return elements.toString();
	}

}
