package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.value.IF.StringValue;

/**
 * Represents an occurrence of a string literal in a program, which is a string
 * surrounded by double quotes. The string may contain various kinds of escape
 * sequences, which have been processed to yield the final "string value". Both
 * the original representation and the string value can be obtained from this
 * class.
 * 
 * @author siegel
 * 
 */
public interface StringLiteralNode extends ExpressionNode {

	/**
	 * Returns the string literal exactly as it occurred in the source code,
	 * with escape sequences, etc.
	 * 
	 * @return original representation in source code
	 */
	String getStringRepresentation();

	/**
	 * Sets the value returned by {@link #getStringRepresentation()}.
	 * 
	 * @param representation
	 *            original representation in source code
	 */
	void setStringRepresentation(String representation);

	/**
	 * The "executed" version of the string in Java: escape sequences have been
	 * replace with the appropriate Java characters, etc.
	 * 
	 * @return string after interpretation
	 */
	StringValue getConstantValue();

	@Override
	StringLiteralNode copy();

}
