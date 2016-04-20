package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.value.IF.Value;

/**
 * A "constant" in the sense of the C11 Standard. See C11 Sec. 6.4.4. Note that
 * C uses the word "constant" in a limited way. Character, integer, and floating
 * point literals and enumeration constants are all considered "constants".
 * String literals and compound literals (array, structure, and union literals)
 * are not considered constants.
 * 
 */
public interface ConstantNode extends ExpressionNode {

	public enum ConstantKind{
		CHAR,
		ENUM,
		FLOAT,
		HERE_OR_ROOT,
		INT,
		PROCNULL,
		/**
		 * A use of the CIVL-C built-in variable <code>$self</code> of type
		 * <code>$proc</code>. It represents the process which is evaluating the
		 * expression containing <code>$self</code>. A node of this kind may be
		 * safely cast to {@link SelfNode}.
		 */
		SELF, 
		STRING
	}
	
	ConstantKind constantKind();
	
	/**
	 * Returns the representation of the constant exactly as it occurred in the
	 * source code.
	 * 
	 * @return the original representation of this constant in the source code
	 */
	String getStringRepresentation();

	/**
	 * Sets the value returned by {@link #getStringRepresentation}.
	 * 
	 * @param representation
	 *            the original representation of this constant in the source
	 *            code
	 */
	void setStringRepresentation(String representation);

	/**
	 * Returns the actual constant value, obtained by evaluating this constant
	 * expression.
	 * 
	 * @return the value of this constant expression
	 */
	Value getConstantValue();

	@Override
	ConstantNode copy();
}
