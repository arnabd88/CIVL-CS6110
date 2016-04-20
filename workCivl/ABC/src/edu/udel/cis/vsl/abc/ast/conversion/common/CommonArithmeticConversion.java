package edu.udel.cis.vsl.abc.ast.conversion.common;

import edu.udel.cis.vsl.abc.ast.conversion.IF.ArithmeticConversion;
import edu.udel.cis.vsl.abc.ast.type.IF.ArithmeticType;

public class CommonArithmeticConversion extends CommonConversion implements
		ArithmeticConversion {

	public CommonArithmeticConversion(ArithmeticType oldType,
			ArithmeticType newType) {
		super(oldType, newType);
	}

	@Override
	public ArithmeticType getOldType() {
		return (ArithmeticType) super.getOldType();
	}

	@Override
	public ArithmeticType getNewType() {
		return (ArithmeticType) super.getNewType();
	}

	@Override
	public String toString() {
		return "Arithmetic" + super.toString();
	}

	@Override
	public ConversionKind conversionKind() {
		return ConversionKind.ARITHMETIC;
	}

}
