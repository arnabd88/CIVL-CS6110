package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;

public class CommonHeapType extends CommonObjectType implements
		UnqualifiedObjectType {

	private static int classCode = CommonHeapType.class.hashCode();

	public CommonHeapType() {
		super(TypeKind.HEAP);
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
		return object instanceof CommonHeapType;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print("$heap");
	}

	@Override
	public boolean isScalar() {
		return false;
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		return other instanceof CommonHeapType;
	}

}
