package edu.udel.cis.vsl.abc.analysis.entity;

import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;

public class LiteralStructOrUnionTypeNode extends LiteralTypeNode {

	private LiteralTypeNode[] memberNodes;

	public LiteralStructOrUnionTypeNode(StructureOrUnionType type,
			LiteralTypeNode[] memberNodes) {
		super(type);
		this.memberNodes = memberNodes;
	}

	@Override
	public StructureOrUnionType getType() {
		return (StructureOrUnionType) super.getType();
	}

	@Override
	public boolean hasFixedLength() {
		return true;
	}

	@Override
	public int length() {
		return memberNodes.length;
	}

	public LiteralTypeNode getMemberNode(int index) {
		return memberNodes[index];
	}

	@Override
	public String toString() {
		String result;
		boolean first = true;

		if (getType().isStruct())
			result = "Struct";
		else
			result = "Union";
		result += "[";
		for (LiteralTypeNode child : memberNodes) {
			if (first)
				first = false;
			else
				result += ",";
			result += child;
		}
		result += "]";
		return result;
	}

	@Override
	public LiteralTypeNode getChild(int index) {
		return getMemberNode(index);
	}

}
