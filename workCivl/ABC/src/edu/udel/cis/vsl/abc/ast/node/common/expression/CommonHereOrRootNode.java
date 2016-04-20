package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.HereOrRootNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonHereOrRootNode extends CommonConstantNode implements
		HereOrRootNode {
	private boolean isRootNode;

	public CommonHereOrRootNode(Source source, String representation,
			Type scopeType) {
		super(source, representation, scopeType);
		if (representation.equalsIgnoreCase("$root"))
			isRootNode = true;
		else
			isRootNode = false;
	}

	@Override
	public HereOrRootNode copy() {
		String representation = "$here";

		if (isRootNode)
			representation = "$root";
		return new CommonHereOrRootNode(getSource(), representation,
				getInitialType());
	}

	@Override
	public boolean isHereNode() {
		return !this.isRootNode;
	}

	@Override
	public boolean isRootNode() {
		return this.isRootNode;
	}

	@Override
	protected void printBody(PrintStream out) {
		if (isRootNode)
			out.print("$root");
		else
			out.print("$here");
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof HereOrRootNode)
			if (this.isRootNode == ((HereOrRootNode) that).isRootNode())
				return null;
			else
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different $root/$here value");
		return new DifferenceObject(this, that);
	}

	@Override
	public ConstantKind constantKind() {
		return ConstantKind.HERE_OR_ROOT;
	}
}
