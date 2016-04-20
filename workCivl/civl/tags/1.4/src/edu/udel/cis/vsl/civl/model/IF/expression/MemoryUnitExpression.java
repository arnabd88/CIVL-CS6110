package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A memory unit expression is an expression that represents (part of) the
 * memory related to some variable. There are four kinds of such expressions:
 * <ul>
 * <li>SELF: a single variable</li>
 * <li>ARRAY_ELE: an element of an array</li>
 * <li>ARRAY_SLICE: a slice (several elements) of an array</li>
 * <li>STRUCT_ELE: an element of a struct</li>
 * </ul>
 * 
 * @author zmanchun
 *
 */
public interface MemoryUnitExpression extends Expression {

	/**
	 * Returns the (static) scope id of the variable.
	 * 
	 * @return The (static) scope id of the variable.
	 */
	int scopeId();

	/**
	 * Returns the variable ID.
	 * 
	 * @return The variable ID.
	 */
	int variableId();
	
	Variable variable();

	/**
	 * Returns the reference of this memory unit expression.
	 * 
	 * @return The reference of this memory unit expression.
	 */
	MemoryUnitReference reference();

	CIVLType objectType();

	boolean writable();

	boolean hasPointerRef();
}
