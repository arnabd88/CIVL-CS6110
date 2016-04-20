package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

public class CommonPointerType extends CommonObjectType implements PointerType {

	private static int classCode = CommonPointerType.class.hashCode();

	private Type referencedType;

	public CommonPointerType(Type referencedType) {
		super(TypeKind.POINTER);
		this.referencedType = referencedType;
	}

	@Override
	public Type referencedType() {
		return referencedType;
	}

	@Override
	public boolean isComplete() {
		return true;
	}

	@Override
	public boolean isVariablyModified() {
		return referencedType.isVariablyModified();
	}

	@Override
	public int hashCode() {
		int result = classCode + referencedType.hashCode();

		return result;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonPointerType) {
			CommonPointerType that = (CommonPointerType) object;

			return referencedType.equals(that.referencedType);
		}
		return false;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print("Pointer");
		if (referencedType != null) {
			out.println();
			out.print(prefix + "| ");
			referencedType.print(prefix + "| ", out, true);
		}
	}

	@Override
	public String toString() {
		String result = "(" + referencedType + ") *";

		return result;
	}

	@Override
	public boolean isScalar() {
		return true;
	}

	/**
	 * "For two pointer types to be compatible, both shall be identically
	 * qualified and both shall be pointers to compatible types."
	 * 
	 */
	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		if (other instanceof CommonPointerType) {
			CommonPointerType that = (CommonPointerType) other;

			return ((CommonType) referencedType).similar(that.referencedType,
					equivalent, seen);
		}
		return false;
	}
}
