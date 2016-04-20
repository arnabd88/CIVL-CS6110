package edu.udel.cis.vsl.abc.ast.value.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;

public interface ArrayValue extends CompoundValue {

	Value getElement(int index);

	void setElement(int index, Value elementValue);

	@Override
	ArrayType getType();

}
