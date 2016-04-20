package edu.udel.cis.vsl.abc.ast.node.IF.compound;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;

/**
 * <p>
 * A designation node specifies a sequence of designators. Each designator is
 * either an array designator or field designator. The sequence navigates to a
 * point within a compound structure.
 * </p>
 * 
 * <p>
 * The methods inherited from {@link SequenceNode} provide all that is necessary
 * to read and modify the sequence of designators.
 * 
 * @see SequenceNode#numChildren()
 * @see SequenceNode#child(int)
 * @see SequenceNode#addSequenceChild(edu.udel.cis.vsl.abc.ast.node.IF.ASTNode)
 * 
 * @author siegel
 * 
 */
public interface DesignationNode extends SequenceNode<DesignatorNode> {

	@Override
	DesignationNode copy();
}
