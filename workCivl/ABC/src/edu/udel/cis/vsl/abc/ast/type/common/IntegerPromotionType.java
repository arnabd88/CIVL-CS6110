package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;

public class IntegerPromotionType extends CommonIntegerType {

	public static final int classCode = IntegerPromotionType.class.hashCode();

	private IntegerType baseType;

	public IntegerPromotionType(IntegerType baseType) {
		super(TypeKind.OTHER_INTEGER);
		this.baseType = baseType;
	}

	@Override
	public boolean isEnumeration() {
		return false;
	}

	@Override
	public String toString() {
		return "IntegerPromotion[" + baseType + "]";
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print(this);
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof IntegerPromotionType) {
			IntegerPromotionType that = (IntegerPromotionType) object;

			return baseType.equals(that.baseType);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode ^ baseType.hashCode();
	}

}
