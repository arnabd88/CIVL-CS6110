package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsEventNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public abstract class CommonDependsEventNode extends CommonASTNode implements
		DependsEventNode {

	public CommonDependsEventNode(Source source, ASTNode child) {
		super(source, child);
	}

	public CommonDependsEventNode(Source source, ASTNode left, ASTNode right) {
		super(source, left, right);
	}

	public CommonDependsEventNode(Source source) {
		super(source);
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.DEPENDS_EVENT;
	}
}
