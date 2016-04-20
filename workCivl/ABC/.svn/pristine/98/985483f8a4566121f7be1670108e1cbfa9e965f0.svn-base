package edu.udel.cis.vsl.abc.ast.conversion.common;

import edu.udel.cis.vsl.abc.ast.conversion.IF.NullPointerConversion;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;

public class CommonNullPointerConversion extends CommonConversion implements
		NullPointerConversion {

	public CommonNullPointerConversion(ObjectType type1, PointerType type2) {
		super(type1, type2);
	}

	@Override
	public ObjectType getOldType() {
		return (ObjectType) super.getOldType();
	}

	@Override
	public PointerType getNewType() {
		return (PointerType) super.getNewType();
	}

	@Override
	public String toString() {
		return "NullPointer" + super.toString();
	}

	@Override
	public ConversionKind conversionKind() {
		return ConversionKind.NULL_POINTER;
	}
}
