package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompletenessNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonCompletenessNode extends CommonContractNode implements
		CompletenessNode {

	/**
	 * true if this is complete clause, otherwise it is a disjoint clause
	 */
	private boolean isComplete;

	public CommonCompletenessNode(Source source, boolean isComplete,
			SequenceNode<IdentifierNode> idList) {
		super(source, idList);
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.COMPLETENESS;
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<IdentifierNode> getIDList() {
		return (SequenceNode<IdentifierNode>) this.child(0);
	}

	@Override
	public CompletenessNode copy() {
		return new CommonCompletenessNode(getSource(), isComplete,
				duplicate(this.getIDList()));
	}

	@Override
	protected void printBody(PrintStream out) {
		out.println("completeness");
	}

	@Override
	public boolean isDisjoint() {
		return !this.isComplete;
	}

	@Override
	public boolean isComplete() {
		return this.isComplete;
	}

}
