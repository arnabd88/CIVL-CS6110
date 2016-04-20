package edu.udel.cis.vsl.abc.ast.node.common.type;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonStructureOrUnionTypeNode extends CommonTypeNode implements
		StructureOrUnionTypeNode {

	private boolean isStruct;

	private boolean isDefinition;

	public CommonStructureOrUnionTypeNode(Source source, boolean isStruct,
			IdentifierNode tag,
			SequenceNode<FieldDeclarationNode> structDeclList) {
		super(source, TypeNodeKind.STRUCTURE_OR_UNION, tag, structDeclList);
		this.isStruct = isStruct;
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
	public StructureOrUnionType getType() {
		Type type=super.getType();
		
		if (type instanceof QualifiedObjectType){
			return (StructureOrUnionType) ((QualifiedObjectType)type).getBaseType();
		}
		return (StructureOrUnionType) type;
	}

	@Override
	public StructureOrUnionType getEntity() {
		return getType();
	}

	@Override
	public void setEntity(Entity entity) {
		setType((StructureOrUnionType) entity);
	}

	@Override
	public boolean isStruct() {
		return isStruct;
	}

	@Override
	public boolean isUnion() {
		return !isStruct;
	}

	@Override
	public IdentifierNode getTag() {
		return (IdentifierNode) child(0);
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<FieldDeclarationNode> getStructDeclList() {
		return (SequenceNode<FieldDeclarationNode>) child(1);
	}

	@Override
	protected void printBody(PrintStream out) {
		String qualifiers = qualifierString();

		if (isStruct)
			out.print("StructureType");
		else
			out.print("UnionType");
		if (!qualifiers.isEmpty()) {
			out.print("[");
			out.print(qualifierString());
			out.print("]");
		}
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
	public StructureOrUnionTypeNode copy() {
		CommonStructureOrUnionTypeNode result = new CommonStructureOrUnionTypeNode(
				getSource(), isStruct(), duplicate(getTag()),
				duplicate(getStructDeclList()));

		copyData(result);
		return result;
	}

	@Override
	public void makeIncomplete() {
		removeChild(1);
	}

	@Override
	public BlockItemKind blockItemKind() {
		return BlockItemKind.STRUCT_OR_UNION;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof StructureOrUnionTypeNode) {
			StructureOrUnionTypeNode thatType = (StructureOrUnionTypeNode) that;

			if (this.isDefinition == thatType.isDefinition()
					&& this.isStruct == thatType.isStruct())
				return null;
			else
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different definition/struct-or-union specifier");
		}
		return new DifferenceObject(this, that);
	}

}
