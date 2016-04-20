package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Scope;

public interface FunctionIdentifierExpression extends Expression {
	/**
	 * 
	 * @return The scope that the function is declared
	 */
	Scope scope();
	
	CIVLFunction function();
}
