package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.MemoryType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

public class CommonMemoryType extends CommonObjectType implements MemoryType {

	private static int classCode = CommonMemoryType.class.hashCode();

	public CommonMemoryType() {
		super(TypeKind.MEMORY);
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
		return object instanceof CommonMemoryType;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print("$proc");
	}

	@Override
	public boolean isScalar() {
		return true;
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		return other instanceof CommonMemoryType;
	}

}
