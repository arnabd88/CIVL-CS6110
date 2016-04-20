package edu.udel.cis.vsl.abc.ast.value.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.Type;

/**
 * A value obtained by casting a value to a new type.
 * 
 * @author siegel
 * 
 */
public interface CastValue extends Value {

	Type getCastType();

	Value getArgument();

}
