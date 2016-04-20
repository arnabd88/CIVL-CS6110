package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.AtomicType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;

public class CommonAtomicType extends CommonObjectType implements AtomicType {

	private static int classCode = CommonAtomicType.class.hashCode();

	private UnqualifiedObjectType baseType;

	public CommonAtomicType(UnqualifiedObjectType baseType) {
		super(TypeKind.ATOMIC);
		this.baseType = baseType;
	}

	@Override
	public UnqualifiedObjectType getBaseType() {
		return baseType;
	}

	@Override
	public boolean isComplete() {
		return baseType.isComplete();
	}

	@Override
	public boolean isVariablyModified() {
		return baseType.isVariablyModified();
	}

	@Override
	public int hashCode() {
		return classCode ^ baseType.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof CommonAtomicType) {
			CommonAtomicType that = (CommonAtomicType) obj;

			return baseType.equals(that.baseType);
		}
		return false;
	}

	@Override
	public String toString() {
		return "AtomicType[" + baseType + "]";
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.println("Atomic");
		baseType.print(prefix + "| ", out, true);
	}

	@Override
	public boolean isScalar() {
		return baseType.isScalar();
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		if (other instanceof AtomicType) {
			return ((CommonType) baseType).similar(
					((AtomicType) other).getBaseType(), equivalent, seen);
		}
		return false;
	}

}
