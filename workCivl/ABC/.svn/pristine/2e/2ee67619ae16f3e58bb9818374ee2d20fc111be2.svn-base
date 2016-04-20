package edu.udel.cis.vsl.abc.ast.node.common.type;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.Source;

public abstract class CommonTypeNode extends CommonASTNode implements TypeNode {

	private TypeNodeKind typeNodeKind;

	private boolean constQualified = false;

	private boolean volatileQualified = false;

	private boolean restrictQualified = false;

	private boolean atomicQualified = false;

	private boolean inputQualified = false;

	private boolean outputQualified = false;

	private Type type;

	public CommonTypeNode(Source source, TypeNodeKind kind) {
		super(source);
		this.typeNodeKind = kind;
	}

	public CommonTypeNode(Source source, TypeNodeKind kind, ASTNode child) {
		super(source, child);
		this.typeNodeKind = kind;
	}

	public CommonTypeNode(Source source, TypeNodeKind kind, ASTNode child0,
			ASTNode child1) {
		super(source, child0, child1);
		this.typeNodeKind = kind;
	}

	public CommonTypeNode(Source source, TypeNodeKind kind, ASTNode child0,
			ASTNode child1, ASTNode child2) {
		super(source, child0, child1, child2);
		this.typeNodeKind = kind;
	}

	@Override
	public TypeNodeKind kind() {
		return typeNodeKind;
	}

	@Override
	public boolean isConstQualified() {
		return constQualified;
	}

	@Override
	public void setConstQualified(boolean value) {
		this.constQualified = value;
	}

	@Override
	public boolean isVolatileQualified() {
		return volatileQualified;
	}

	@Override
	public void setVolatileQualified(boolean value) {
		this.volatileQualified = value;
	}

	@Override
	public boolean isRestrictQualified() {
		return restrictQualified;
	}

	@Override
	public void setRestrictQualified(boolean value) {
		this.restrictQualified = value;
	}

	@Override
	public boolean isAtomicQualified() {
		return atomicQualified;
	}

	@Override
	public void setAtomicQualified(boolean value) {
		this.atomicQualified = value;
	}

	@Override
	public boolean isInputQualified() {
		return inputQualified;
	}

	@Override
	public void setInputQualified(boolean value) {
		this.inputQualified = value;
	}

	@Override
	public boolean isOutputQualified() {
		return outputQualified;
	}

	@Override
	public void setOutputQualified(boolean value) {
		this.outputQualified = value;
	}

	@Override
	public Type getType() {
		return type;
	}

	@Override
	public void setType(Type type) {
		this.type = type;
	}

	protected String qualifierString() {
		String result = typeId();
		boolean needSeparator = true;

		if (constQualified) {
			if (needSeparator)
				result += ", ";
			result = "const";
			needSeparator = true;
		}
		if (volatileQualified) {
			if (needSeparator)
				result += ", ";
			result += "volatile";
			needSeparator = true;
		}
		if (restrictQualified) {
			if (needSeparator)
				result += ", ";
			result += "restrict";
			needSeparator = true;
		}
		if (atomicQualified) {
			if (needSeparator)
				result += ", ";
			result += "atomic";
		}
		return result;
	}

	protected String typeId() {
		if (type == null)
			return "type=UNKNOWN";
		else
			return "type=" + type.getId();
	}

	protected void copyData(TypeNode node) {
		node.setAtomicQualified(isAtomicQualified());
		node.setConstQualified(isConstQualified());
		node.setInputQualified(isInputQualified());
		node.setOutputQualified(isOutputQualified());
		node.setRestrictQualified(isRestrictQualified());
		node.setVolatileQualified(isVolatileQualified());
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.TYPE;
	}

	@Override
	public TypeNodeKind typeNodeKind() {
		return typeNodeKind;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof TypeNode) {
			TypeNode thatType = (TypeNode) that;

			if (this.typeNodeKind == thatType.typeNodeKind()
					&& this.atomicQualified == thatType.isAtomicQualified()
					&& this.constQualified == thatType.isConstQualified()
					&& this.inputQualified == thatType.isInputQualified()
					&& this.outputQualified == thatType.isOutputQualified()
					&& this.restrictQualified == thatType.isRestrictQualified()
					&& this.volatileQualified == thatType.isVolatileQualified())
				return null;
			else
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different qualifiers");
		}
		return new DifferenceObject(this, that, DiffKind.KIND);
	}
}
