package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ContractVerifyNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonContractVerifyNode extends CommonFunctionCallNode implements
		ContractVerifyNode {

	public CommonContractVerifyNode(Source source, ExpressionNode function,
			SequenceNode<ExpressionNode> contextArguments,
			SequenceNode<ExpressionNode> arguments,
			SequenceNode<ExpressionNode> scopeList) {
		super(source, function, contextArguments, arguments, scopeList);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("ContractVerifyNode");
	}

	@Override
	public FunctionCallNode copy() {
		@SuppressWarnings("unchecked")
		SequenceNode<ExpressionNode> contextArguments = (SequenceNode<ExpressionNode>) child(1);
		@SuppressWarnings("unchecked")
		SequenceNode<ExpressionNode> arguments = (SequenceNode<ExpressionNode>) child(2);
		@SuppressWarnings("unchecked")
		SequenceNode<ExpressionNode> scopeList = (SequenceNode<ExpressionNode>) child(3);

		return new CommonContractVerifyNode(getSource(),
				duplicate(getFunction()), duplicate(contextArguments),
				duplicate(arguments), duplicate(scopeList));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.CONTRACT_VERIFY;
	}

}
