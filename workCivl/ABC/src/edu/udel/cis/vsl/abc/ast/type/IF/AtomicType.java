package edu.udel.cis.vsl.abc.ast.type.IF;

/**
 * <p>
 * An atomic type, specified by <code>_Atomic ( type-name )</code> or by using
 * the <code>_Atomic</code> type qualifier. See C11 Sec. 6.7.2.4.
 * </p>
 * 
 * <p>
 * The base type cannot be array, function, atomic, or qualified.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface AtomicType extends UnqualifiedObjectType {

	/**
	 * Returns the base type.
	 * 
	 * @return the base type
	 */
	UnqualifiedObjectType getBaseType();

}
