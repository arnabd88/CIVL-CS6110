package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;

public interface CivlParForEnterStatement extends Statement {

	CIVLFunction parProcFunction();

	Expression domain();

	int dimension();

	VariableExpression domSizeVar();

	Expression parProcsPointer();

	VariableExpression parProcsVar();
	
	void setParProcFunction(CIVLFunction function);
}
