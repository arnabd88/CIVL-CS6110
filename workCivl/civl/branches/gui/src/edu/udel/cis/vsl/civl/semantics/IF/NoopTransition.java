package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

public interface NoopTransition extends Transition {

	BooleanExpression assumption();
}
