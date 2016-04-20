package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.value.IF.AddressValue;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public abstract class CommonAddressValue extends CommonValue implements
		AddressValue {

	CommonAddressValue(PointerType type) {
		super(type);
	}

	@Override
	public PointerType getType() {
		return (PointerType) super.getType();
	}

	@Override
	public Answer isZero() {
		return Answer.NO;
	}

}
