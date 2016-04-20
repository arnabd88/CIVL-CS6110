package edu.udel.cis.vsl.abc.ast.entity.IF;

import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;

/**
 * A label followed by a colon may precede a statement in a C program. This
 * entity represents the label. It simply wraps an instance of
 * {@link OrdinaryLabelNode}, the node corresponding to the label.
 * 
 * @author siegel
 * 
 */
public interface Label extends ProgramEntity {

	/**
	 * Returns the node representing the label.
	 * 
	 * @return the label node
	 */
	OrdinaryLabelNode getDefinition();
}
