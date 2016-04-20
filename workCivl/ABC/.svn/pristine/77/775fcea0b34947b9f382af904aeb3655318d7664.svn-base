package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;

/**
 * Conversion of a null pointer constant to any pointer type.
 * 
 * <blockquote> An integer constant expression with the value 0, or such an
 * expression cast to type <code>void *</code>, is called a null pointer
 * constant. If a null pointer constant is converted to a pointer type, the
 * resulting pointer, called a null pointer, is guaranteed to compare unequal to
 * a pointer to any object or function. </blockquote>
 * 
 * Also:
 * 
 * <blockquote> Conversion of a null pointer to another pointer type yields a
 * null pointer of that type. Any two null pointers shall compare equal.
 * </blockquote>
 * 
 * @author siegel
 * 
 */
public interface NullPointerConversion extends Conversion {

	/**
	 * An integer type or <code>void*</code>.
	 */
	@Override
	ObjectType getOldType();

	/**
	 * A pointer type.
	 */
	@Override
	PointerType getNewType();

}
