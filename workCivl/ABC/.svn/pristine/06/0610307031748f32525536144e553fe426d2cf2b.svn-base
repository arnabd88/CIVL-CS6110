package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.value.IF.VariableReference;

public class CommonVariableReference extends CommonAddressValue implements
		VariableReference {

	private final static int classCode = CommonVariableReference.class
			.hashCode();

	private Variable variable;

	public CommonVariableReference(PointerType type, Variable variable) {
		super(type);
		this.variable = variable;
	}

	@Override
	public String toString() {
		return "VariableReference[" + variable + "]";
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonVariableReference) {
			return variable.equals(((CommonVariableReference) object).variable);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + variable.hashCode();
	}

	@Override
	public Variable getVariable() {
		return variable;
	}

}
