package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.math.BigInteger;

import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;

public class RangeChoiceType extends CommonIntegerType implements IntegerType {

	private final static int classCode = RangeChoiceType.class.hashCode();

	private BigInteger value;

	private IntegerType type1;

	private IntegerType type2;

	public RangeChoiceType(BigInteger value, IntegerType type1,
			IntegerType type2) {
		super(TypeKind.OTHER_INTEGER);
		this.value = value;
		this.type1 = type1;
		this.type2 = type2;
	}

	@Override
	public boolean isEnumeration() {
		return false;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print(this);
	}

	@Override
	public String toString() {
		return "if " + value + " in range of " + type1 + " then " + type1
				+ " else " + type2;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof RangeChoiceType) {
			RangeChoiceType that = (RangeChoiceType) object;

			return type1.equals(that.type1) && type2.equals(that.type2)
					&& value.equals(that.value);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + type1.hashCode() + type2.hashCode()
				+ value.hashCode();
	}

}
