package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
/**
 * 
 * @author zmanchun
 *
 */
public interface StructOrUnionLiteralExpression extends LiteralExpression {
	Expression[] fields();

	void setFields(Expression[] fields);
	
	CIVLStructOrUnionType structOrUnionType();
	
	boolean isStruct();
}
