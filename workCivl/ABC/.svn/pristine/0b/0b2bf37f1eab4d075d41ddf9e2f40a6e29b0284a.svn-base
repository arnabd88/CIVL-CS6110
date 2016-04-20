package edu.udel.cis.vsl.abc.ast.type.common;

import edu.udel.cis.vsl.abc.ast.entity.IF.CommonEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;

public class CommonField extends CommonEntity implements Field {

	private Value bitWidth;

	private int memberIndex;

	public CommonField(FieldDeclarationNode declaration, ObjectType type,
			Value bitWidth) {
		super(EntityKind.FIELD, declaration.getName(), ProgramEntity.LinkageKind.NONE);
		addDeclaration(declaration);
		setDefinition(declaration);
		this.bitWidth = bitWidth;
		setType(type);
		this.memberIndex = declaration.childIndex();
	}

	@Override
	public FieldDeclarationNode getDefinition() {
		return (FieldDeclarationNode) super.getDefinition();
	}

	@Override
	public ObjectType getType() {
		return (ObjectType) super.getType();
	}

	@Override
	public Value getBitWidth() {
		return bitWidth;
	}

	@Override
	public int getMemberIndex() {
		return memberIndex;
	}

}
