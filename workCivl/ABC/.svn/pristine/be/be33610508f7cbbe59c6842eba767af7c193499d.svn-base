package edu.udel.cis.vsl.abc.ast.type.common;

import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

public abstract class CommonIntegerType extends CommonObjectType implements
		IntegerType {

	public CommonIntegerType(TypeKind kind) {
		super(kind);
	}

	@Override
	public boolean isInteger() {
		return true;
	}

	@Override
	public boolean isFloating() {
		return false;
	}

	@Override
	public boolean inRealDomain() {
		return true;
	}

	@Override
	public boolean inComplexDomain() {
		return false;
	}

	@Override
	public boolean isComplete() {
		return true;
	}

	@Override
	public boolean isVariablyModified() {
		return false;
	}

	@Override
	public boolean isScalar() {
		return true;
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		return equals(other);
	}

}
