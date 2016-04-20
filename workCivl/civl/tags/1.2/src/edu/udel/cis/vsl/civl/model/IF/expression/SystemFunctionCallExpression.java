package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

public interface SystemFunctionCallExpression extends Expression {
	CallOrSpawnStatement callStatement();

	void setExpressionType(CIVLType returnType);
}
