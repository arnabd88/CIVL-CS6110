package edu.udel.cis.vsl.abc.ast.conversion.common;

import edu.udel.cis.vsl.abc.ast.conversion.IF.RegularRangeToDomainConversion;
import edu.udel.cis.vsl.abc.ast.type.IF.DomainType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;

public class CommonRegularRangeToDomainConversion extends CommonConversion
		implements RegularRangeToDomainConversion {

	public CommonRegularRangeToDomainConversion(ObjectType oldType,
			DomainType newType) {
		super(oldType, newType);
	}

	@Override
	public ObjectType getOldType() {
		return (ObjectType) super.getOldType();
	}

	@Override
	public DomainType getNewType() {
		return (DomainType) super.getNewType();
	}

	@Override
	public ConversionKind conversionKind() {
		return ConversionKind.REG_RANGE_DOMAIN;
	}
}
