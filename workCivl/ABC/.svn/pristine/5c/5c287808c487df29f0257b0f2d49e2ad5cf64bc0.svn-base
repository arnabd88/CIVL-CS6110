package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;

/**
 * This represents the completeness clause of ACSL, which could be either
 * <code>complete</code> or <code>disjoint</code>
 * 
 * <pre>
 * complete behaviors (id0, id1, ...)?
 * </pre>
 * 
 * or
 * 
 * *
 * 
 * <pre>
 * disjoint behaviors (id0, id1, ...)?
 * </pre>
 * 
 * 
 * @author Manchun Zheng
 *
 */
public interface CompletenessNode extends ContractNode {

	/**
	 * The list of behavior IDs associates with this completeness clause.
	 * 
	 * @return
	 */
	SequenceNode<IdentifierNode> getIDList();

	@Override
	CompletenessNode copy();

	/**
	 * Is this a disjoint clause?
	 * 
	 * @return
	 */
	boolean isDisjoint();

	/**
	 * Is this a complete clause?
	 * 
	 * @return
	 */
	boolean isComplete();
}
