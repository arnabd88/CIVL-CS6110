package edu.udel.cis.vsl.abc.ast.node.IF.type;

import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;

public interface BasicTypeNode extends TypeNode {

	BasicTypeKind getBasicTypeKind();

	@Override
	BasicTypeNode copy();

}
