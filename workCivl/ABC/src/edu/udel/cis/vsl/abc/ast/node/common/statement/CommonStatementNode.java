package edu.udel.cis.vsl.abc.ast.node.common.statement;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public abstract class CommonStatementNode extends CommonASTNode implements
		StatementNode {

	public CommonStatementNode(Source source) {
		super(source);
	}

	public CommonStatementNode(Source source, ASTNode child) {
		super(source, child);
	}

	public CommonStatementNode(Source source, ASTNode child0, ASTNode child1) {
		super(source, child0, child1);
	}

	public CommonStatementNode(Source source, ASTNode child0, ASTNode child1,
			ASTNode child2) {
		super(source, child0, child1, child2);
	}

	@Override
	public BlockItemKind blockItemKind() {
		return BlockItemKind.STATEMENT;
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.STATEMENT;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof StatementNode)
			if (this.statementKind() == ((StatementNode) that).statementKind())
				return null;
		return new DifferenceObject(this, that);
	}

}
