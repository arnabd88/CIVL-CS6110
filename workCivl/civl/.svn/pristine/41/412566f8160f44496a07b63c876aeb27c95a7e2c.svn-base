package edu.udel.cis.vsl.civl.model.IF.type;

import java.util.Collection;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.Identifier;

/**
 * Represents a "struct" or "record" type. This is essentially a tuple type with
 * a name.
 * 
 * This type has state. Initially, it is incomplete, meaning the component types
 * are not specified. It is completed by specifying them. This is necessary to
 * allow circular definitions such as linked lists.
 * 
 * @author siegel
 * 
 */
public interface CIVLStructType extends CIVLType {

	/**
	 * Is this struct type complete?
	 * 
	 * @return true iff this is complete
	 */
	boolean isComplete();

	/**
	 * Returns the number of fields in this struct typel
	 * 
	 * @throws CIVLInternalException
	 *             if the type is not complete
	 * @return the number of fields
	 */
	int numFields();

	/**
	 * Returns the index-th field of this struct type.
	 * 
	 * @param index
	 *            nonnegative integer in range [0,numFields-1].
	 * 
	 * @return the index-th field
	 * @throws CIVLInternalException
	 *             if this type is not complete
	 */
	StructField getField(int index);

	/**
	 * Returns an iterable object over all the fields of this struct type, in
	 * ascending order.
	 * 
	 * @return A list of the field types in this struct.
	 * @throws CIVLInternalException
	 *             if this type is not complete
	 */
	Iterable<StructField> fields();

	/**
	 * Returns the name of this struct type.
	 * 
	 * @return The name of this struct.
	 */
	Identifier name();

	/**
	 * Completes this struct type by specifying the fields as a collection.
	 * 
	 * @param fields
	 *            the fields
	 * @throws CIVLInternalException
	 *             if this struct type is already complete
	 */
	void complete(Collection<StructField> fields);

	/**
	 * Completes this struct type by specifying the fields as an array. The
	 * array is copied.
	 * 
	 * @param fields
	 *            the fields
	 * @throws CIVLInternalException
	 *             if this struct type is already complete
	 */
	void complete(StructField[] fields);
}
