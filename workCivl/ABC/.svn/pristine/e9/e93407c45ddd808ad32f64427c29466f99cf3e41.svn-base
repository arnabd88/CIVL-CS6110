package edu.udel.cis.vsl.abc.ast.node.IF.compound;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;

/**
 * A field designator is used in an initializer for a struct or union. It is a
 * reference to a particular member (field) of that struct or union.
 * 
 * @author siegel
 * 
 */
public interface FieldDesignatorNode extends DesignatorNode {

	/**
	 * The name of the field being designated for initialization.
	 * 
	 * @return the field name
	 * @see #setField(IdentifierNode)
	 */
	IdentifierNode getField();

	/**
	 * Sets the name of the field being designated for initialization.
	 * 
	 * @param name
	 *            the field name
	 * @see #getField()
	 */
	void setField(IdentifierNode name);

	@Override
	FieldDesignatorNode copy();
}
