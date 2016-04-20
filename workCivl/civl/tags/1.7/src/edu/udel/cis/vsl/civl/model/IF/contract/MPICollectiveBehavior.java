package edu.udel.cis.vsl.civl.model.IF.contract;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

public interface MPICollectiveBehavior extends FunctionBehavior {
	public static enum MPICommunicationPattern {
		P2P, COL
	};

	Expression communicator();

	MPICommunicationPattern mpiCommunicationPattern();

	void addNamedBehaviors(NamedFunctionBehavior namedBehavior);

	List<NamedFunctionBehavior> namedBehaviors();

	NamedFunctionBehavior namedBahavior(String name);
}
