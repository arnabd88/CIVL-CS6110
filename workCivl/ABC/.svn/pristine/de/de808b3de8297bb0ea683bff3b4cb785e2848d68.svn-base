package edu.udel.cis.vsl.abc.ast.conversion.common;

import edu.udel.cis.vsl.abc.ast.conversion.IF.LvalueConversion;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;

public class CommonLvalueConversion extends CommonConversion implements
		LvalueConversion {

	public CommonLvalueConversion(ObjectType oldType,
			UnqualifiedObjectType newType) {
		super(oldType, newType);
	}

	@Override
	public ObjectType getOldType() {
		return (ObjectType) super.getOldType();
	}

	@Override
	public UnqualifiedObjectType getNewType() {
		return (UnqualifiedObjectType) super.getNewType();
	}

	@Override
	public String toString() {
		return "Lvalue" + super.toString();
	}

	@Override
	public ConversionKind conversionKind() {
		return ConversionKind.LVALUE;
	}

}
