package edu.udel.cis.vsl.abc.ast.node.common.type;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonArrayTypeNode extends CommonTypeNode implements
		ArrayTypeNode {

	private boolean unspecifiedVariableLength = false;

	private boolean staticExtent = false;

	private boolean constInBrackets = false;

	private boolean volatileInBrackets = false;

	private boolean restrictInBrackets = false;

	private boolean atomicInBrackets = false;
	
	private boolean hasStartIndex = false;

	public CommonArrayTypeNode(Source source, TypeNode elementType,
			ExpressionNode extent) {
		super(source, TypeNodeKind.ARRAY, elementType, extent);
	}

	public CommonArrayTypeNode(Source source, TypeNode elementType,
			ExpressionNode extent, ExpressionNode startIndex) {
		super(source, TypeNodeKind.ARRAY, elementType, extent, startIndex);
		this.hasStartIndex = true;
	}

	@Override
	public TypeNode getElementType() {
		return (TypeNode) child(0);
	}

	@Override
	public void setElementType(TypeNode elementType) {
		setChild(0, elementType);
	}

	@Override
	public ExpressionNode getExtent() {
		return (ExpressionNode) child(1);
	}

	@Override
	public void setExtent(ExpressionNode extent) {
		setChild(1, extent);
	}

	@Override
	public boolean hasUnspecifiedVariableLength() {
		return unspecifiedVariableLength;
	}

	@Override
	public void setUnspecifiedVariableLength(boolean value) {
		unspecifiedVariableLength = value;
	}

	@Override
	public boolean hasStaticExtent() {
		return staticExtent;
	}

	@Override
	public void setStaticExtent(boolean value) {
		staticExtent = value;
	}

	@Override
	public void printBody(PrintStream out) {
		String qualifiers = qualifierString();
		boolean needSeparator = !qualifiers.isEmpty();

		out.print("Array[" + qualifiers);
		if (unspecifiedVariableLength) {
			if (needSeparator)
				out.print(", ");
			out.print("unspecifiedVariableLength");
			needSeparator = true;
		}
		if (staticExtent) {
			if (needSeparator)
				out.print(", ");
			out.print("staticExtent");
		}
		out.print("]");
	}

	@Override
	public boolean hasConstInBrackets() {
		return constInBrackets;
	}

	@Override
	public void setConstInBrackets(boolean value) {
		constInBrackets = value;
	}

	@Override
	public boolean hasVolatileInBrackets() {
		return volatileInBrackets;
	}

	@Override
	public void setVolatileInBrackets(boolean value) {
		volatileInBrackets = value;
	}

	@Override
	public boolean hasRestrictInBrackets() {
		return restrictInBrackets;
	}

	@Override
	public void setRestrictInBrackets(boolean value) {
		restrictInBrackets = value;
	}

	@Override
	public boolean hasAtomicInBrackets() {
		return atomicInBrackets;
	}

	@Override
	public void setAtomicInBrackets(boolean value) {
		atomicInBrackets = value;
	}

	@Override
	public ArrayTypeNode copy() {
		CommonArrayTypeNode result = new CommonArrayTypeNode(getSource(),
				duplicate(getElementType()), duplicate(getExtent()));

		copyData(result);
		result.setAtomicInBrackets(this.hasAtomicInBrackets());
		result.setConstInBrackets(this.hasConstInBrackets());
		result.setRestrictInBrackets(this.hasRestrictInBrackets());
		result.setStaticExtent(this.hasStaticExtent());
		result.setUnspecifiedVariableLength(this.hasUnspecifiedVariableLength());
		result.setVolatileInBrackets(this.hasVolatileInBrackets());
		return result;
	}

	@Override
	public ExpressionNode getStartIndex() {
		return (ExpressionNode) child(2);
	}

	@Override
	public void setStartIndex(ExpressionNode startIndex) {
		setChild(2, startIndex);
		this.hasStartIndex = true;
	}

	@Override
	public boolean hasStartIndex() {
		return hasStartIndex;
	}

}
