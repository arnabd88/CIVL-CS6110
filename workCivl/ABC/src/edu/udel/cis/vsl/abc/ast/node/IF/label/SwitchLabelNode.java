package edu.udel.cis.vsl.abc.ast.node.IF.label;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * Represents a label in a <code>switch</code> statement of the form
 * <code>case constant-expression:</code> or <code>default:</code>.
 * 
 * @author siegel
 * 
 */
public interface SwitchLabelNode extends LabelNode {

	/**
	 * Is this a <code>default</code> label?
	 * 
	 * @return <code>true</code> if this is a <code>default</code> label;
	 *         <code>false</code> if this is a <code>case</code> label
	 */
	boolean isDefault();

	/**
	 * If this is a <code>case</code> label, returns the constant expression
	 * following the <code>case</code> keyword; else returns <code>null</code>
	 * 
	 * @return the constant expression following <code>case</code> or
	 *         <code>null</code>
	 */
	ExpressionNode getExpression();

	@Override
	SwitchLabelNode copy();

}
