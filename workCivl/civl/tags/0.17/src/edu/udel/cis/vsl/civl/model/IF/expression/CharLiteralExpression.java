package edu.udel.cis.vsl.civl.model.IF.expression;

public interface CharLiteralExpression extends LiteralExpression {

	/**
	 * 
	 * @return The char value.
	 */
	char value();

	/**
	 * Update the value of this char literal.
	 * 
	 * @param value
	 *            The char to be used as the value of the char literal.
	 */
	void setValue(char value);
}
