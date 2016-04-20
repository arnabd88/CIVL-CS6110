package edu.udel.cis.vsl.abc.ast.node.common.compound;

import java.util.List;

import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonSequenceNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonDesignationNode extends CommonSequenceNode<DesignatorNode>
		implements DesignationNode {

	public CommonDesignationNode(Source source, List<DesignatorNode> childList) {
		super(source, "DesignatorList", childList);
	}

	@Override
	public DesignationNode copy() {
		return new CommonDesignationNode(getSource(), childListCopy());
	}

}
