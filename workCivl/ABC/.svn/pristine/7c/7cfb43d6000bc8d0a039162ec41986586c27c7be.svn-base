package edu.udel.cis.vsl.abc.ast.type.IF;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;

/**
 * <p>
 * Represents an array type. See C11 Sec. 6.7.6.2.
 * </p>
 * 
 * <p>
 * Note that in certain contexts type qualifiers may also occur between the
 * square brackets in the array type designation. These will be determined by
 * calling the appropriate qualifier methods in {@link TypeNode}.
 * </p>
 * 
 * <p>
 * An array type is an object type specified by an element type and the extent.
 * The element type must be a complete object type. For the extent, there are 4
 * possibilities:
 * </p>
 * 
 * <p>
 * NOTE: the keyword <code>static</code> can only appear in the outermost part
 * of the declaration of a function parameter, and since the types are converted
 * to pointer, <code>static</code> does not ultimately occur in an array type.
 * On the other hand <code>*</code> can occur in any number of internal array
 * types in a function parameter, so it can ultimately be part of an array type.
 * </p>
 * 
 * <ol>
 * <li>the extent is not specified (i.e., is null): then the array type is an
 * "incomplete type"</li>
 * <li>the extent is <code>*</code>: this is a "VLA type of unspecified size".
 * It is nevertheless a complete type. This can only be used in declarations or
 * type names in function prototype scope (i.e., in a function declaration that
 * is not part of a function definition).</li>
 * <li>the extent is an integer constant expression AND the element type has
 * known constant size: then the array type is "not a VLA" type. It is complete.
 * (Note: an object type has "known constant size" iff it is not incomplete AND
 * not a VLA (Variable Length Array) type.)</li>
 * <li>otherwise, the extent is an expression which is not a constant
 * expression. This is a VLA type. It is complete. If it occurs in function
 * prototype scope, it is treated as if it were <code>*</code> (i.e., the
 * expression is not used).</li>
 * </ol>
 * 
 * 
 * @author siegel
 * 
 */
public interface ArrayType extends UnqualifiedObjectType {

	/**
	 * The type of the elements. This is required and must be non-null.
	 * 
	 * @return the element type
	 */
	ObjectType getElementType();

	/**
	 * The expression appearing in square brackets that specifies the length of
	 * the array, when that length is not a known constant. If the length in
	 * brackets is a known constant, or is "*", or is absent, this will return
	 * <code>null</code>.
	 * 
	 * @return the variable array extent expression or <code>null</code>
	 */
	ExpressionNode getVariableSize();

	/**
	 * If this array has a known constant extent, it is returned by this method.
	 * Otherwise, this method returns <code>null</code>.
	 * 
	 * @return the known constant extent or <code>null</code>
	 */
	IntegerValue getConstantSize();

	/**
	 * Is this a Variable Length Array (VLA) type?
	 * 
	 * @return true iff this is a VLA type
	 */
	boolean isVariableLengthArrayType();

	/**
	 * In C11, a star (<code>*</code>) may appear between the square brackets
	 * instead of an integer expression. The star represents "a variable length
	 * array type of unspecified size, which can only be used in declarations or
	 * type names with function prototype scope." See C11 Sec. 6.7.6.2(4).
	 * 
	 * @return true if a <code>*</code> occurs between the brackets
	 */
	boolean hasUnspecifiedVariableLength();

}
