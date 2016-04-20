package edu.udel.cis.vsl.abc.ast.node.common.omp;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpFunctionReductionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonOmpFunctionReductionNode extends CommonOmpReductionNode
		implements OmpFunctionReductionNode {

	public CommonOmpFunctionReductionNode(Source source,
			IdentifierExpressionNode identifier,
			SequenceNode<IdentifierExpressionNode> variables) {
		super(source);
		this.addChild(identifier);
		this.addChild(variables);
	}

	@Override
	public OmpReductionNodeKind ompReductionOperatorNodeKind() {
		return OmpReductionNodeKind.FUNCTION;
	}

	@Override
	public ASTNode copy() {
		return null;
	}

	@Override
	public IdentifierExpressionNode function() {
		return (IdentifierExpressionNode) this.child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("OmpFunctionReductionNode");
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<IdentifierExpressionNode> variables() {
		return (SequenceNode<IdentifierExpressionNode>) this.child(1);
	}
}
