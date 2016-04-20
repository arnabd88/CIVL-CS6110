package edu.udel.cis.vsl.abc.ast.type.common;

import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;

public abstract class CommonObjectType extends CommonType implements ObjectType {

	public CommonObjectType(TypeKind kind) {
		super(kind);
	}

	/**
	 * Does this type have known constant size? An object type has
	 * "known constant size" iff it is not incomplete AND not a VLA (Variable
	 * Length Array) type.
	 * 
	 * @return true iff this is an object type of known constant size
	 */
	@Override
	public boolean hasKnownConstantSize() {
		return isComplete()
				&& !(this instanceof ArrayType && ((ArrayType) this)
						.isVariableLengthArrayType());
	}

	@Override
	public boolean isConstantQualified() {
		return false;
	}

}
