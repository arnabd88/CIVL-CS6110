package edu.udel.cis.vsl.abc.ast.node.IF.label;

import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.Label;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;

/**
 * <p>
 * Represents an ordinary label (i.e., a label which is not a <code>case</code>
 * or <code>default</code> label).
 * </p>
 * 
 * <p>
 * A label may precede a statement, as in <code>l1: x=1;</code>. An instance of
 * this class is used to represent the <code>l1</code>. It contains a reference
 * to the statement which it precedes.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface OrdinaryLabelNode extends LabelNode, DeclarationNode {

	/**
	 * Returns the Label entity defined by this label node.
	 * 
	 * @return the Label entity corresponding to this label node
	 */
	@Override
	Label getEntity();

	/**
	 * The function in which this label occurs. A label has "function scope".
	 * 
	 * @return the function in which this label occurs
	 */
	Function getFunction();

	/**
	 * Sets the value returned by {@link #getFunction()}.
	 * 
	 * @param function
	 *            the function in which this label occurs
	 */
	void setFunction(Function function);

	@Override
	OrdinaryLabelNode copy();

}
