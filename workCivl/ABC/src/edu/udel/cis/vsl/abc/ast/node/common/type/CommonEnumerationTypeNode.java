package edu.udel.cis.vsl.abc.ast.node.common.type;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonEnumerationTypeNode extends CommonTypeNode implements
		EnumerationTypeNode {

	boolean isDefinition = false;

	public CommonEnumerationTypeNode(Source source, IdentifierNode tag,
			SequenceNode<EnumeratorDeclarationNode> enumerators) {
		super(source, TypeNodeKind.ENUMERATION, tag, enumerators);
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
		isDefinition = value;
	}

	@Override
	public IdentifierNode getTag() {
		return (IdentifierNode) child(0);
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<EnumeratorDeclarationNode> enumerators() {
		return (SequenceNode<EnumeratorDeclarationNode>) child(1);
	}

	@Override
	public void makeIncomplete() {
		removeChild(1);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("Enumeration[" + qualifierString() + "]");
	}

	@Override
	public String getName() {
		IdentifierNode tag = getTag();

		if (tag == null)
			return null;
		else
			return tag.name();
	}

	@Override
	public EnumerationType getType() {
		return (EnumerationType) super.getType();
	}

	@Override
	public EnumerationType getEntity() {
		return getType();
	}

	@Override
	public void setEntity(Entity entity) {
		setType((EnumerationType) entity);
	}

	@Override
	public EnumerationTypeNode copy() {
		CommonEnumerationTypeNode result = new CommonEnumerationTypeNode(
				getSource(), duplicate(getTag()), duplicate(enumerators()));

		copyData(result);
		return result;
	}

	@Override
	public BlockItemKind blockItemKind() {
		return BlockItemKind.ENUMERATION;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof EnumerationTypeNode)
			if (this.isDefinition == ((EnumerationTypeNode) that)
					.isDefinition())
				return null;
			else
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different definition specifier");
		return new DifferenceObject(this, that);
	}

}
