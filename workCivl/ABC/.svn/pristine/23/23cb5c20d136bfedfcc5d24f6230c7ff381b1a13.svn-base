package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;

/**
 * An implicit conversion from array type to pointer type. In C, an expression
 * of array type in most cases is converted to a pointer to the first element of
 * the array.  From C11 Sec. 6.3.2.1:
 * 
 * <blockquote> Except when it is the operand of the sizeof operator, the
 * <code>_Alignof</code> operator, or the unary & operator, or is a string
 * literal used to initialize an array, an expression that has type
 * "array of type" is converted to an expression with type "pointer to type"
 * that points to the initial element of the array object and is not an lvalue.
 * If the array object has register storage class, the behavior is undefined.
 * </blockquote>
 * 
 * @author siegel
 * 
 */
public interface ArrayConversion extends Conversion {

	@Override
	ArrayType getOldType();

	@Override
	PointerType getNewType();

}
