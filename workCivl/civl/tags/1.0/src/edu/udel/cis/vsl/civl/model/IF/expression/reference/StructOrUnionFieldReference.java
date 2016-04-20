package edu.udel.cis.vsl.civl.model.IF.expression.reference;

/**
 * This represents a reference to a field of a struct/union.
 * 
 * @author Manchun Zheng (zmanchun)
 *
 */
public interface StructOrUnionFieldReference extends MemoryUnitReference {
	/**
	 * The field index of this reference.
	 * 
	 * @return
	 */
	int fieldIndex();
}
