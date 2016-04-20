package edu.udel.cis.vsl.abc.ast.conversion.common;

import edu.udel.cis.vsl.abc.ast.conversion.IF.FunctionConversion;
import edu.udel.cis.vsl.abc.ast.type.IF.FunctionType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;

public class CommonFunctionConversion extends CommonConversion implements
		FunctionConversion {

	public CommonFunctionConversion(FunctionType oldType, PointerType newType) {
		super(oldType, newType);
	}

	@Override
	public FunctionType getOldType() {
		return (FunctionType) super.getOldType();
	}

	@Override
	public PointerType getNewType() {
		return (PointerType) super.getNewType();
	}

	@Override
	public String toString() {
		return "Function" + super.toString();
	}

	@Override
	public ConversionKind conversionKind() {
		return ConversionKind.FUNCTION;
	}

}
