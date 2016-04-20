package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;

public class CommonScopeType extends CommonObjectType implements
		UnqualifiedObjectType {

	private static int classCode = CommonScopeType.class.hashCode();

	public CommonScopeType() {
		super(TypeKind.SCOPE);
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
	public int hashCode() {
		return classCode;
	}

	@Override
	public boolean equals(Object object) {
		return object instanceof CommonScopeType;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print("$scope");
	}

	@Override
	public boolean isScalar() {
		return false;
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		return other instanceof CommonScopeType;
	}

	@Override
	public String toString() {
		return "$scope";
	}
}
