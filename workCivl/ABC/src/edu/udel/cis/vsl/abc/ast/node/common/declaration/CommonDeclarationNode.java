package edu.udel.cis.vsl.abc.ast.node.common.declaration;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public abstract class CommonDeclarationNode extends CommonASTNode implements
		DeclarationNode {

	private boolean isDefinition = false;

	private Entity entity = null;

	public CommonDeclarationNode(Source source, IdentifierNode identifier) {
		super(source, identifier);
	}

	public CommonDeclarationNode(Source source, IdentifierNode identifier,
			ASTNode child1) {
		super(source, identifier, child1);
	}

	public CommonDeclarationNode(Source source, IdentifierNode identifier,
			ASTNode child1, ASTNode child2) {
		super(source, identifier, child1, child2);
	}

	public CommonDeclarationNode(Source source, IdentifierNode identifier,
			ASTNode child1, ASTNode child2, ASTNode child3) {
		super(source, identifier, child1, child2, child3);
	}

	@Override
	public IdentifierNode getIdentifier() {
		return (IdentifierNode) child(0);
	}

	@Override
	public void setIdentifier(IdentifierNode identifier) {
		setChild(0, identifier);
	}

	@Override
	public boolean isDefinition() {
		return isDefinition;
	}

	@Override
	public void setIsDefinition(boolean value) {
		this.isDefinition = value;
	}

	@Override
	public Entity getEntity() {
		return entity;
	}

	@Override
	public void setEntity(Entity entity) {
		this.entity = entity;
	}

	@Override
	public String getName() {
		IdentifierNode identifier = getIdentifier();

		if (identifier == null)
			return null;
		else
			return identifier.name();
	}

}
