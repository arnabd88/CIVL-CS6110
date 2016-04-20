package edu.udel.cis.vsl.abc.ast.entity.common;

import edu.udel.cis.vsl.abc.ast.entity.IF.CommonEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Label;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;

public class CommonLabel extends CommonEntity implements Label {

	public CommonLabel(OrdinaryLabelNode declaration) {
		super(EntityKind.LABEL, declaration.getName(), ProgramEntity.LinkageKind.NONE);
		addDeclaration(declaration);
		setDefinition(declaration);
	}

	@Override
	public OrdinaryLabelNode getDefinition() {
		return (OrdinaryLabelNode) super.getDefinition();
	}

}
