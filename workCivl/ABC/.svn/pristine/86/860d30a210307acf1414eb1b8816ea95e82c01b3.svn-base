package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

/**
 * Represents the sort of "join" of two integer types: this is the least integer
 * type that is a supertype of the two given integer types.
 * 
 * @author siegel
 *
 */
public class ArithmeticConversionType extends CommonIntegerType {

	public final static int classCode = ArithmeticConversionType.class
			.hashCode();

	private IntegerType type1;

	private IntegerType type2;

	public ArithmeticConversionType(IntegerType type1, IntegerType type2) {
		super(TypeKind.OTHER_INTEGER);

		this.type1 = type1;
		this.type2 = type2;
	}

	@Override
	public boolean isEnumeration() {
		return false;
	}

	@Override
	public String toString() {
		return "ArithmeticConversionType[" + type1 + ", " + type2 + "]";
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print(this);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof ArithmeticConversionType) {
			ArithmeticConversionType that = (ArithmeticConversionType) obj;

			// the arithmetic conversion type represents the sort of
			// "join" of type1 and type2. It is a commutative operator,
			// so order doesn't matter:
			return type1.equals(that.type1) && type2.equals(that.type2)
					|| type2.equals(that.type1) && type1.equals(that.type2);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + type1.hashCode() + type2.hashCode();
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		if (other instanceof ArithmeticConversionType) {
			ArithmeticConversionType that = (ArithmeticConversionType) other;
			CommonType t11 = (CommonType) type1, t12 = (CommonType) type2;
			CommonType t21 = (CommonType) that.type1, t22 = (CommonType) that.type2;

			return t11.similar(t21, equivalent, seen)
					&& t12.similar(t22, equivalent, seen)
					|| t12.similar(t22, equivalent, seen)
					&& t11.similar(t22, equivalent, seen);
		}
		return false;
	}
}
