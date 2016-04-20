package edu.udel.cis.vsl.abc.analysis.entity;

import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;

public class LiteralArrayTypeNode extends LiteralTypeNode {

	private LiteralTypeNode elementNode;

	private int length;

	private boolean fixed;

	public LiteralArrayTypeNode(ArrayType type, LiteralTypeNode elementNode) {
		super(type);

		IntegerValue constantSize = type.getConstantSize();

		this.elementNode = elementNode;
		assert elementNode.getType().equals(type.getElementType());
		if (constantSize != null) {
			length = constantSize.getIntegerValue().intValue();
			fixed = true;
		} else {
			length = 0;
			fixed = false;
		}
	}

	@Override
	public ArrayType getType() {
		return (ArrayType) super.getType();
	}

	@Override
	public boolean hasFixedLength() {
		return fixed;
	}

	@Override
	public int length() {
		return length;
	}

	public LiteralTypeNode getElementNode() {
		return elementNode;
	}

	@Override
	public String toString() {
		return "Array[" + length + "," + getElementNode() + "]";
	}

	public void setLength(int value) {
		assert !fixed;
		this.length = value;
	}

	@Override
	public LiteralTypeNode getChild(int index) {
		return getElementNode();
	}

}
