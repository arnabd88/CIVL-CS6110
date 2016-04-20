package edu.udel.cis.vsl.civl.model.IF.type;

import java.util.Collection;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.Identifier;

/**
 * Represents a "record" type (i.e. a struct or union). This is essentially a
 * tuple type with a name.
 * 
 * This type has state. Initially, it is incomplete, meaning the component types
 * are not specified. It is completed by specifying them. This is necessary to
 * allow circular definitions such as linked lists.
 * 
 * Two CIVL struct or union types are considered equal iff they are equal as
 * objects. They can be different even if the fields and names are equal.
 * 
 * @author siegel
 * 
 */
public interface CIVLStructOrUnionType extends CIVLType {

	/**
	 * Is this struct or union type complete?
	 * 
	 * @return true iff this is complete
	 */
	boolean isComplete();

	/**
	 * Returns the number of fields in this struct or union type.
	 * 
	 * @throws CIVLInternalException
	 *             if the type is not complete
	 * @return the number of fields
	 */
	int numFields();

	/**
	 * Returns the index-th field of this struct or union type.
	 * 
	 * @param index
	 *            nonnegative integer in range [0,numFields-1].
	 * 
	 * @return the index-th field
	 * @throws CIVLInternalException
	 *             if this type is not complete
	 */
	StructOrUnionField getField(int index);

	/**
	 * Returns an iterable object over all the fields of this struct type, in
	 * ascending order.
	 * 
	 * @return A list of the field types in this struct.
	 * @throws CIVLInternalException
	 *             if this type is not complete
	 */
	Iterable<StructOrUnionField> fields();

	/**
	 * Returns the name of this struct or union type.
	 * 
	 * @return The name of this struct or union.
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
	void complete(Collection<StructOrUnionField> fields);

	/**
	 * Completes this struct type by specifying the fields as an array. The
	 * array is copied.
	 * 
	 * @param fields
	 *            the fields
	 * @throws CIVLInternalException
	 *             if this struct type is already complete
	 */
	void complete(StructOrUnionField[] fields);

	/**
	 * Updates the option whether this type is the object type of some handle
	 * type, with the given value.
	 * 
	 * @param value
	 *            The value to be used.
	 */
	void setHandleObjectType(boolean value);

	int getFieldIndex(String field);
}
