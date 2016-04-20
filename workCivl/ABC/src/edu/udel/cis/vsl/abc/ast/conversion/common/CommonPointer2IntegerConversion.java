package edu.udel.cis.vsl.abc.ast.conversion.common;

import edu.udel.cis.vsl.abc.ast.conversion.IF.Pointer2IntegerConversion;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;

public class CommonPointer2IntegerConversion extends CommonConversion implements
		Pointer2IntegerConversion {

	public CommonPointer2IntegerConversion(PointerType oldType,
			IntegerType newType) {
		super(oldType, newType);
	}

	@Override
	public ConversionKind conversionKind() {
		return ConversionKind.POINTER_INTEGER;
	}

	@Override
	public PointerType getOldType() {
		return (PointerType) super.getOldType();
	}

	@Override
	public IntegerType getNewType() {
		return (IntegerType) super.getNewType();
	}
}
