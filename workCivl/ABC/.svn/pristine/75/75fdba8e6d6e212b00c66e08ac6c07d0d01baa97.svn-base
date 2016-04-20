package edu.udel.cis.vsl.abc.ast.conversion.common;

import edu.udel.cis.vsl.abc.ast.conversion.IF.Integer2PointerConversion;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;

public class CommonInteger2PointerConversion extends CommonConversion implements
		Integer2PointerConversion {

	public CommonInteger2PointerConversion(IntegerType oldType,
			PointerType newType) {
		super(oldType, newType);
	}

	@Override
	public IntegerType getOldType() {
		return (IntegerType) super.getOldType();
	}

	@Override
	public PointerType getNewType() {
		return (PointerType) super.getNewType();
	}

	@Override
	public ConversionKind conversionKind() {
		return ConversionKind.INTEGER_POINTER;
	}

}
