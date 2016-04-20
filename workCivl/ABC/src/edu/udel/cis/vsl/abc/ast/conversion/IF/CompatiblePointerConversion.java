package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;

/**
 * An implicit conversion from one pointer type to another pointer type in the
 * case where either the two types are compatible or the second type is obtained
 * by adding a qualifier to the type of thing pointed to. From C11 Sec. 6.3.2.3:
 * 
 * <blockquote> For any qualifier q, a pointer to a non-q-qualified type may be
 * converted to a pointer to the q-qualified version of the type; the values
 * stored in the original and converted pointers shall compare equal.
 * </blockquote>
 * 
 * From C11 Sec. 6.7.6.1:
 * 
 * <blockquote> For two pointer types to be compatible, both shall be
 * identically qualified and both shall be pointers to compatible types.
 * </blockquote>
 * 
 * @author siegel
 * 
 */
public interface CompatiblePointerConversion extends Conversion {

	@Override
	PointerType getOldType();

	@Override
	PointerType getNewType();
}
