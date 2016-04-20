package edu.udel.cis.vsl.abc.ast.type.IF;

import edu.udel.cis.vsl.abc.ast.entity.IF.TaggedEntity;

/**
 * An enumeration type. An enumeration type consists of a key, a tag, and a
 * sequence of enumerators. The key is used to determine when two enumeration
 * types are equal. Each enumerator consists of an identifier and an optional
 * constant expression.
 * 
 * @author siegel
 */
public interface EnumerationType extends IntegerType, TaggedEntity {

	/**
	 * Returns the key associated to this instance. The key is used in the
	 * determination of equality of two instances of EnumerationType.
	 * 
	 * @return the key
	 */
	Object getKey();

	/**
	 * Returns the tag of this enumeration type. This is the string used in the
	 * declaration of the type, i.e., in "enum foo {...}", "foo" is the tag.
	 * 
	 * @return the tag of this enumeration type
	 */
	String getTag();

	/**
	 * Returns the number of enumerators specified in this enumeration type.
	 * 
	 * @exception RuntimeException
	 *                if the type is not complete, i.e., the enumerators have
	 *                not yet been specified
	 * 
	 * @return the number of enumerators in the type
	 */
	int getNumEnumerators();

	/**
	 * Returns the index-th enumerator defined in the type.
	 * 
	 * @param index
	 *            an integer between 0 and the number of enumerators minus 1,
	 *            inclusive
	 * @return the index-th enumerator
	 * 
	 * @exception RuntimeException
	 *                if the type is not complete
	 */
	Enumerator getEnumerator(int index);

	/**
	 * Returns the sequence of enumerators for this enumerated type. Each
	 * enumerator consists of a name and optional constant expression. If the
	 * optional constant expression is absent, it will be null.
	 * 
	 * This will return <code>null</code> if the type is incomplete, i.e., the
	 * enumerators have not yet been specified
	 * 
	 * @return the sequence node for the enumerators of this type, or
	 *         <code>null</code>
	 */
	Iterable<Enumerator> getEnumerators();

	/**
	 * Completes this enumeration type by specifying the contents of the type,
	 * i.e., the list or enumerator constants.
	 * 
	 * @param enumerators
	 *            an ordered list of enumerators which comprise the type
	 * 
	 * @exception RuntimeException
	 *                if the type is already complete
	 */
	void complete(Iterable<Enumerator> enumerators);

	/**
	 * Makes this type incomplete, i.e., sets the enumerators to
	 * <code>null</code>.
	 */
	void clear();

	@Override
	EnumerationType getType();
}
