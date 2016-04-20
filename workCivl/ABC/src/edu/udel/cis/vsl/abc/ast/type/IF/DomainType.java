package edu.udel.cis.vsl.abc.ast.type.IF;

/**
 * The CIVL-C type <code>$domain</code> or <code>$domain(n)</code>.
 * 
 * @author siegel
 * 
 */
public interface DomainType extends UnqualifiedObjectType {

	/**
	 * Does this domain type have a specified dimension?
	 * 
	 * @return <code>true</code> iff the dimension is specified
	 */
	boolean hasDimension();

	/**
	 * Returns the dimension, or -1 if the dimension is not specified.
	 * 
	 * @return dimension or -1
	 */
	int getDimension();

}
