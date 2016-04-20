package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;

/**
 * some sv-comp examples are using conversions between pointers and integers.
 * this conversion would only be used when -svcomp option is on.
 * 
 * @author zmanchun
 *
 */
public interface Pointer2IntegerConversion extends Conversion {
	@Override
	PointerType getOldType();

	@Override
	IntegerType getNewType();
}
