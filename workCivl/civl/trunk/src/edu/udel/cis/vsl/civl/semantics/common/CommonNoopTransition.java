package edu.udel.cis.vsl.civl.semantics.common;

import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.NoopTransition;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

public class CommonNoopTransition extends CommonTransition implements
		NoopTransition {

	private BooleanExpression assumption;

	public CommonNoopTransition(BooleanExpression pathCondition, int pid,
			int processIdentifier, BooleanExpression assumption,
			Statement statement, boolean symplifyState,
			AtomicLockAction atomicLockAction) {
		super(pathCondition, pid, processIdentifier, statement, symplifyState,
				atomicLockAction);
		this.assumption = assumption;
	}

	@Override
	public TransitionKind transitionKind() {
		return TransitionKind.NOOP;
	}

	@Override
	public BooleanExpression assumption() {
		return this.assumption;
	}
}
