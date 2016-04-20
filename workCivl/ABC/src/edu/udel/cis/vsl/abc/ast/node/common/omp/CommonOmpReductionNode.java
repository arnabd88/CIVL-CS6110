package edu.udel.cis.vsl.abc.ast.node.common.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public abstract class CommonOmpReductionNode extends CommonASTNode
		implements OmpReductionNode {

	public CommonOmpReductionNode(Source source) {
		super(source);
		// TODO Auto-generated constructor stub
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.OMP_REDUCTION_OPERATOR;
	}
}
