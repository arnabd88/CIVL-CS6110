package edu.udel.cis.vsl.civl.model.common.contract;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.NamedFunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.common.CommonSourceable;

public class CommonFunctionContract extends CommonSourceable implements
		FunctionContract {

	private boolean pure = false;

	private Expression guard = null;

	private FunctionBehavior defaultBehavior;

	private List<MPICollectiveBehavior> mpiCollectiveBehaviors = null;

	private HashMap<String, NamedFunctionBehavior> namedBehaviors = new HashMap<>();

	public CommonFunctionContract(CIVLSource source) {
		super(source);
		defaultBehavior = new CommonFunctionBehavior(source);
	}

	@Override
	public FunctionBehavior defaultBehavior() {
		return this.defaultBehavior;
	}

	@Override
	public Iterable<NamedFunctionBehavior> namedBehaviors() {
		return this.namedBehaviors.values();
	}

	@Override
	public Expression guard() {
		return this.guard;
	}

	@Override
	public void setGuard(Expression expression) {
		this.guard = expression;
	}

	@Override
	public void setDefaultBehavior(FunctionBehavior behavior) {
		this.defaultBehavior = behavior;
	}

	@Override
	public void addNamedBehavior(NamedFunctionBehavior behavior) {
		this.namedBehaviors.put(behavior.name(), behavior);
	}

	@Override
	public NamedFunctionBehavior getBehavior(String name) {
		return this.namedBehaviors.get(name);
	}

	@Override
	public void print(String prefix, PrintStream out, boolean isDebug) {
		String subPrefix = prefix + "| ";

		out.println(prefix + "contract");
		if (this.pure)
			out.println(subPrefix + "pure");
		if (guard != null)
			out.println(subPrefix + "guard: " + guard.toString());
		defaultBehavior.print(subPrefix, out, isDebug);
		for (NamedFunctionBehavior behavior : namedBehaviors.values()) {
			behavior.print(subPrefix, out, isDebug);
		}
	}

	@Override
	public boolean isPure() {
		return this.pure;
	}

	@Override
	public void setPure(boolean value) {
		this.pure = value;
	}

	@Override
	public boolean hasReadsClause() {
		return this.defaultBehavior.readsNothing()
				|| defaultBehavior.numReadsMemoryUnits() > 0;
	}

	@Override
	public boolean hasAssignsClause() {
		return defaultBehavior.assignsNothing()
				|| defaultBehavior.numAssignsMemoryUnits() > 0;
	}

	@Override
	public boolean hasDependsClause() {
		return defaultBehavior.dependsAnyact()
				|| defaultBehavior.dependsNoact()
				|| defaultBehavior.numDependsEvents() > 0;
	}

	@Override
	public boolean hasRequirementsOrEnsurances() {
		return (defaultBehavior.numEnsurances() + defaultBehavior
				.numRequirements()) > 0;
	}

	@Override
	public void addMPICollectiveBehavior(MPICollectiveBehavior behavior) {
		if (mpiCollectiveBehaviors == null)
			mpiCollectiveBehaviors = new LinkedList<>();
		mpiCollectiveBehaviors.add(behavior);
	}

	@Override
	public Iterator<MPICollectiveBehavior> getMPIBehaviors() {
		if (mpiCollectiveBehaviors == null)
			mpiCollectiveBehaviors = new LinkedList<>();
		return mpiCollectiveBehaviors.iterator();
	}

}
