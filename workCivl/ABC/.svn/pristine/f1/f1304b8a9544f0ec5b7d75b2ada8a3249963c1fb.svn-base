package edu.udel.cis.vsl.abc.ast.node.IF.declaration;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;

/**
 * The declaration of an enumerator (enumeration constant) within an enumeration
 * type definition.
 * 
 * @author siegel
 * 
 */
public interface EnumeratorDeclarationNode extends DeclarationNode {

	/**
	 * Each enumerator in an enumeration type definition may have an optional
	 * constant value specified. This method returns the constant expression for
	 * that value, if the value is present. Otherwise, returns <code>null</code>
	 * 
	 * @return the specified constant value for this enumerator, else null
	 * @see #setValue(ExpressionNode)
	 */
	ExpressionNode getValue();

	/**
	 * Sets the optional value expression to the given expression node.
	 * 
	 * @param value
	 *            a constant integer expression
	 */
	void setValue(ExpressionNode value);

	@Override
	Enumerator getEntity();

	@Override
	EnumeratorDeclarationNode copy();

}
