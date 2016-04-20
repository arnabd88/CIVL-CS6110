package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;

/**
 * <p>
 * A conversion between the type pointer-to-void and a pointer to an object
 * type. Can convert in either direction.
 * </p>
 * 
 * <p>
 * One operand is a pointer to an object type, and the other is a pointer to a
 * qualified or unqualified version of void, and the type pointed to by the left
 * has all the qualifiers of the type pointed to by the right.
 * </p>
 * 
 * 
 * @author siegel
 * 
 */
public interface VoidPointerConversion extends Conversion {

	@Override
	PointerType getOldType();

	@Override
	PointerType getNewType();

}
