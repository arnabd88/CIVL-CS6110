package edu.udel.cis.vsl.civl.model.common.contract;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.NamedFunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonMPICollectiveBehavior extends CommonFunctionBehavior
		implements MPICollectiveBehavior {
	private Expression communicator;

	private MPICommunicationPattern pattern;

	private List<NamedFunctionBehavior> namedBehaviors = null;

	private Variable[] agreedVariables;

	public CommonMPICollectiveBehavior(CIVLSource source,
			Expression communicator, MPICommunicationPattern pattern) {
		super(source);
		this.communicator = communicator;
		this.pattern = pattern;
	}

	@Override
	public Expression communicator() {
		return communicator;
	}

	@Override
	public MPICommunicationPattern mpiCommunicationPattern() {
		return pattern;
	}

	@Override
	public void addNamedBehaviors(NamedFunctionBehavior namedBehavior) {
		if (namedBehaviors == null)
			namedBehaviors = new LinkedList<>();
		namedBehaviors.add(namedBehavior);
	}

	@Override
	public List<NamedFunctionBehavior> namedBehaviors() {
		if (namedBehaviors == null)
			namedBehaviors = new LinkedList<>();
		return namedBehaviors;
	}

	@Override
	public NamedFunctionBehavior namedBahavior(String name) {
		for (NamedFunctionBehavior namedB : namedBehaviors)
			if (namedB.name().equals(name))
				return namedB;
		return null;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append("mpi_collective[kind=" + pattern + ", comm="
				+ communicator + "]:\n");
		for (Expression requires : this.requirements())
			result.append("  requires " + requires.toString() + ";\n");
		for (Expression ensures : this.ensurances())
			result.append("  ensures  " + ensures.toString() + ";\n");

		return result.toString();
	}

	@Override
	public Variable[] agreedVariables() {
		if (this.agreedVariables == null)
			this.agreedVariables = new Variable[0];
		return this.agreedVariables;
	}

	@Override
	public void setAgreedVariables(Variable[] variables) {
		this.agreedVariables = variables;
	}
}
