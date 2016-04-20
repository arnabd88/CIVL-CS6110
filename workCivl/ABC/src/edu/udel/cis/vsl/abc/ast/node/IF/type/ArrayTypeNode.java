package edu.udel.cis.vsl.abc.ast.node.IF.type;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * Represents an array type. See C11 Sec. 6.7.6.2.
 * 
 * Note that in certain contexts type qualifiers may also occur between the
 * square brackets in the array type designation. These will be determined by
 * calling the appropriate qualifier methods in TypeNode.
 * 
 * @author siegel
 * 
 */
public interface ArrayTypeNode extends TypeNode {

	/**
	 * The type of the elements. This is required and must be non-null.
	 * 
	 * @return the element type
	 */
	TypeNode getElementType();

	void setElementType(TypeNode elementType);

	/**
	 * The expression appearing in square brackets that specifies the length of
	 * the array. This is optional. If absent, this method will return null.
	 * 
	 * @return the array extent expression
	 */
	ExpressionNode getExtent();

	void setExtent(ExpressionNode extent);

	/**
	 * The expression appearing in square brackets that specifies the starting
	 * index of the array. This is optional. If absent, this method will return
	 * null, which represents 0-index as default.
	 * 
	 * @return the array extent expression
	 */
	ExpressionNode getStartIndex();

	void setStartIndex(ExpressionNode startIndex);

	/**
	 * In C11, a star ("*") may appear between the square brackets instead of an
	 * integer expression. The star represents "a variable length array type of
	 * unspecified size, which can only be used in declarations or type names
	 * with function prototype scope." See C11 Sec. 6.7.6.2(4).
	 * 
	 * @return true if a "*" occurs between the brackets
	 */
	boolean hasUnspecifiedVariableLength();

	void setUnspecifiedVariableLength(boolean value);

	/**
	 * The word "static" may appear between the brackets in certain situations.
	 * See C11 6.7.6.3.7 for its meaning.
	 */
	boolean hasStaticExtent();

	void setStaticExtent(boolean value);

	boolean hasConstInBrackets();

	void setConstInBrackets(boolean value);

	boolean hasVolatileInBrackets();

	void setVolatileInBrackets(boolean value);

	boolean hasRestrictInBrackets();

	void setRestrictInBrackets(boolean value);

	boolean hasAtomicInBrackets();

	void setAtomicInBrackets(boolean value);
	
	boolean hasStartIndex();

	@Override
	ArrayTypeNode copy();

}
