package edu.udel.cis.vsl.abc.analysis.entity;

import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;

public class LiteralScalarTypeNode extends LiteralTypeNode {

	public LiteralScalarTypeNode(ObjectType type) {
		super(type);
	}

	@Override
	public boolean hasFixedLength() {
		return true;
	}

	@Override
	public int length() {
		return 0;
	}

	@Override
	public String toString() {
		return getType().toString();
	}

	@Override
	public LiteralTypeNode getChild(int index) {
		throw new ABCRuntimeException("should never be called");
	}

}
