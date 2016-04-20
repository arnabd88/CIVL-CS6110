package edu.udel.cis.vsl.abc.ast.entity.common;

import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Typedef;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

public class CommonTypedef extends CommonOrdinaryEntity implements Typedef {

	public CommonTypedef(String name, Type type) {
		super(EntityKind.TYPEDEF, name, ProgramEntity.LinkageKind.NONE, type);
	}

	@Override
	public TypedefDeclarationNode getDefinition() {
		return (TypedefDeclarationNode) super.getDefinition();
	}

}
