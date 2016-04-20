/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * A dot expression is a reference to a field in a struct or union.
 * 
 * @author zirkel
 * 
 */
public interface DotExpression extends LHSExpression {

	/**
	 * @return The struct or union referenced by this dot expression.
	 */
	Expression structOrUnion();

	/**
	 * @return Index of the field/member referenced by this dot expression.
	 */
	int fieldIndex();
	
	boolean isStruct();
	
	boolean isUnion();

}
