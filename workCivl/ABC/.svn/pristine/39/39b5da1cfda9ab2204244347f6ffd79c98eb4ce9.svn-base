package edu.udel.cis.vsl.abc.ast.value.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public interface Value {

	/**
	 * Returns the type of this value.
	 * 
	 * @return the type of this value
	 */
	Type getType();

	/**
	 * A scalar value is a value of scalar type or a value of union type for
	 * which the single union member is scalar.
	 * 
	 * @return <code>true</code> iff the type of this value is a scalar type
	 */
	boolean isScalar();

	/**
	 * Is this value zero? Can only be asked of scalar values.
	 * 
	 * @return <code>true</code> if this is zero
	 */
	Answer isZero();

}
