package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonBehaviorNode extends CommonContractNode implements
		BehaviorNode {

	public CommonBehaviorNode(Source source, IdentifierNode name,
			SequenceNode<ContractNode> child) {
		super(source, name, (ASTNode) child);
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.BEHAVIOR;
	}

	@Override
	public IdentifierNode getName() {
		return (IdentifierNode) this.child(0);
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<ContractNode> getBody() {
		return (SequenceNode<ContractNode>) this.child(1);
	}

	@Override
	public BehaviorNode copy() {
		return new CommonBehaviorNode(getSource(), duplicate(getName()),
				duplicate(getBody()));
	}

	@Override
	protected void printBody(PrintStream out) {
		out.println("behavior");
	}

}
