package edu.udel.cis.vsl.civl.semantics.common;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

public interface CIVLUnaryOperator<SymbolicExpression> {
	SymbolicExpression apply(BooleanExpression context,
			SymbolicExpression value, CIVLType type);
}
