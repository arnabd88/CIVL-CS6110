package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

/**
 * An expression of the form "sizeof(t)" where t is a type.
 * 
 * @author siegel
 * 
 */
public interface SizeofTypeExpression extends Expression {

	/**
	 * Returns the CIVL type, which is the sole argument of the sizeof operator.
	 * 
	 * @return the CIVL type we are computing the size of
	 */
	CIVLType getTypeArgument();

}
