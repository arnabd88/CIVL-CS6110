package edu.udel.cis.vsl.abc.ast.conversion.common;

import edu.udel.cis.vsl.abc.ast.conversion.IF.MemoryConversion;
import edu.udel.cis.vsl.abc.ast.type.IF.MemoryType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

public class CommonMemoryConversion extends CommonConversion implements
		MemoryConversion {

	public CommonMemoryConversion(Type oldType, MemoryType newType) {
		super(oldType, newType);
	}

	@Override
	public MemoryType getNewType() {
		return (MemoryType) super.getNewType();
	}

	@Override
	public String toString() {
		return "Memory" + super.toString();
	}

	@Override
	public ConversionKind conversionKind() {
		return ConversionKind.MEMORY;
	}

}
