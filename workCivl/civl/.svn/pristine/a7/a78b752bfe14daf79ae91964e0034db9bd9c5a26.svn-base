package edu.udel.cis.vsl.civl.state.trans;

public interface Transient {

	/**
	 * Is this instance mutable?
	 * 
	 * @return true iff this is mutable
	 */
	boolean isMutable();

	/**
	 * Is this insance canonic, i.e., the canonic representative of its
	 * equivalence class under the Flyweight Pattern?
	 * 
	 * @return true iff this is a canonic instance
	 */
	boolean isCanonic();

	/**
	 * Makes this instance canonic.
	 * 
	 * @param canonicId
	 *            the canonic ID number
	 */
	void makeCanonic(int canonicId);

	/**
	 * Makes this instance immutable.
	 */
	void commit();

	/**
	 * Returns the canonic ID number of this instance, or -1 if this is not
	 * canonic. The canonic instances of DynamicState are numbered with unique
	 * IDs starting from 0.
	 * 
	 * @return canonic ID number or -1
	 */
	int getCanonicId();

	/**
	 * The string of the form canonicId:instanceId. Used to easily identify this
	 * instance.
	 * 
	 * @return string canonicId:instanceId
	 */
	String identifier();

}
