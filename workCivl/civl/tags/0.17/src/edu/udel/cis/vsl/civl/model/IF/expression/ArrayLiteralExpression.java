package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

public interface ArrayLiteralExpression extends LiteralExpression {

	Expression[] elements();

	void setElements(Expression[] elements);

	CIVLArrayType arrayType();

	CIVLType elementType();

//	/**
//	 * Return the unique ID of this array literal. Only valid when this literal
//	 * is used to initialize a pointer type variable, otherwise, id should be
//	 * -1.
//	 * 
//	 * @return
//	 */
//	int id();
//	
//	/**
//	 * 
//	 * @param id
//	 */
//	void setId(int id);
}
