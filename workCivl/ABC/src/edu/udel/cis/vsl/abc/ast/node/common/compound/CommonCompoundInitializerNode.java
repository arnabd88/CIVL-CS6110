package edu.udel.cis.vsl.abc.ast.node.common.compound;

import java.io.PrintStream;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundLiteralObject;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonSequenceNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonCompoundInitializerNode extends
		CommonSequenceNode<PairNode<DesignationNode, InitializerNode>>
		implements CompoundInitializerNode {

	private CompoundLiteralObject literal;

	private ObjectType type;

	public CommonCompoundInitializerNode(Source source,
			List<PairNode<DesignationNode, InitializerNode>> childList) {
		super(source, "CompoundInitializer", childList);
	}

	@Override
	public void setLiteralObject(CompoundLiteralObject literal) {
		this.literal = literal;
	}

	@Override
	public CompoundInitializerNode copy() {
		CommonCompoundInitializerNode result = new CommonCompoundInitializerNode(
				getSource(), childListCopy());

		return result;
	}

	@Override
	public CompoundLiteralObject getLiteralObject() {
		return literal;
	}

	@Override
	public void setType(ObjectType type) {
		this.type = type;
	}

	@Override
	public ObjectType getType() {
		return type;
	}

	protected void printExtras(String prefix, PrintStream out) {
		if (literal != null) {
			out.println();
			out.println(prefix + "type: " + type);
			out.print(prefix + "value: " + literal);
		}
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		boolean result = true;

		for (PairNode<DesignationNode, InitializerNode> pair : this) {
			InitializerNode init = pair.getRight();

			result = result && init.isSideEffectFree(errorsAreSideEffects);
		}
		return result;
	}

}
