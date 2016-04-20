package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.value.IF.FunctionReference;

public class CommonFunctionReference extends CommonAddressValue implements
		FunctionReference {

	private final static int classCode = CommonFunctionReference.class
			.hashCode();

	private Function function;

	public CommonFunctionReference(PointerType type, Function function) {
		super(type);
		this.function = function;
	}

	@Override
	public String toString() {
		return "FunctionReference[" + function + "]";
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonFunctionReference) {
			return function.equals(((CommonFunctionReference) object).function);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + function.hashCode();
	}

	@Override
	public Function getFunction() {
		return function;
	}

}
