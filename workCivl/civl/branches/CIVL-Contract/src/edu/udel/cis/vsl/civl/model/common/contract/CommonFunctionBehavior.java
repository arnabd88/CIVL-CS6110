package edu.udel.cis.vsl.civl.model.common.contract;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.common.CommonSourceable;

public class CommonFunctionBehavior extends CommonSourceable implements
		FunctionBehavior {

	private Set<Expression> preconditions = new HashSet<>();

	private Set<Expression> postconditions = new HashSet<>();

	private Set<Expression> assignsMemoryUnits = new HashSet<>();

	private Set<Expression> readsMemoryUnits = new HashSet<>();

	private Set<DependsEvent> dependsEvents = new HashSet<>();

	private boolean assignsNothing = false;

	private boolean readsNothing = false;

	private boolean dependsNoact = false;

	private boolean dependsAnyact = false;

	public CommonFunctionBehavior(CIVLSource source) {
		super(source);
	}

	@Override
	public Iterable<Expression> requirements() {
		return this.preconditions;
	}

	@Override
	public Iterable<Expression> ensurances() {
		return this.postconditions;
	}

	@Override
	public Iterable<Expression> assignsMemoryUnits() {
		return this.assignsMemoryUnits;
	}

	@Override
	public Iterable<Expression> readsMemoryUnits() {
		return this.readsMemoryUnits;
	}

	@Override
	public Iterable<DependsEvent> dependsEvents() {
		return this.dependsEvents;
	}

	@Override
	public void addPrecondition(Expression condition) {
		this.preconditions.add(condition);
	}

	@Override
	public void addPostcondition(Expression condition) {
		this.postconditions.add(condition);
	}

	@Override
	public void addAssignsMemoryUnit(Expression mu) {
		assert !this.assignsNothing;
		this.assignsMemoryUnits.add(mu);
	}

	@Override
	public void addReadsMemoryUnit(Expression mu) {
		assert !this.readsNothing;
		this.readsMemoryUnits.add(mu);
	}

	@Override
	public void addDependsEvent(DependsEvent event) {
		assert !this.dependsNoact;
		this.dependsEvents.add(event);
	}

	@Override
	public int numRequirements() {
		return this.preconditions.size();
	}

	@Override
	public int numEnsurances() {
		return this.postconditions.size();
	}

	@Override
	public int numAssignsMemoryUnits() {
		return this.assignsMemoryUnits.size();
	}

	@Override
	public int numReadsMemoryUnits() {
		return this.readsMemoryUnits.size();
	}

	@Override
	public int numDependsEvents() {
		return this.dependsEvents.size();
	}

	@Override
	public boolean readsNothing() {
		return this.readsNothing;
	}

	@Override
	public boolean assignsNothing() {
		return this.assignsNothing;
	}

	@Override
	public void setReadsNothing() {
		assert this.numReadsMemoryUnits() == 0;
		this.readsNothing = true;
	}

	@Override
	public void setAssingsNothing() {
		assert this.numAssignsMemoryUnits() == 0;
		this.assignsNothing = true;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean isDebug) {
		if (this.numRequirements() > 0) {
			boolean first = true;

			out.print(prefix + "precondition: ");
			for (Expression expression : this.preconditions) {
				if (!first)
					out.print(" && ");
				else
					first = false;
				out.print(expression.toString());
			}
			out.println();
		}
		if (this.numEnsurances() > 0) {
			boolean first = true;

			out.print(prefix + "postcondition: ");
			for (Expression expression : this.postconditions) {
				if (!first)
					out.print(" && ");
				else
					first = false;
				out.print(expression.toString());
			}
			out.println();
		}
		if (assignsNothing)
			out.println(prefix + "assigns nothing");
		else if (this.numAssignsMemoryUnits() > 0) {
			boolean first = true;

			out.print(prefix + "assigns ");
			for (Expression mu : this.assignsMemoryUnits) {
				if (!first)
					out.print(", ");
				else
					first = false;
				out.print(mu.toString());
			}
			out.println();
		}
		if (readsNothing)
			out.println(prefix + "reads nothing");
		else if (this.numReadsMemoryUnits() > 0) {
			boolean first = true;

			out.print(prefix + "reads ");
			for (Expression mu : this.readsMemoryUnits) {
				if (!first)
					out.print(", ");
				else
					first = false;
				out.print(mu.toString());
			}
			out.println();
		}
		if (this.dependsNoact)
			out.println(prefix + "depends noact");
		else if (this.dependsAnyact)
			out.println(prefix + "depends anyact");
		else if (this.numDependsEvents() > 0) {
			boolean first = true;

			out.print(prefix + "depends ");
			for (DependsEvent event : this.dependsEvents) {
				if (!first)
					out.print(", ");
				else
					first = false;
				out.print(event.toString());
			}
			out.println();
		}
	}

	@Override
	public boolean dependsNoact() {
		return this.dependsNoact;
	}

	@Override
	public boolean dependsAnyact() {
		return this.dependsAnyact;
	}

	@Override
	public void setDependsNoact() {
		assert !dependsAnyact && this.numDependsEvents() == 0;
		this.dependsNoact = true;
	}

	@Override
	public void setDependsAnyact() {
		assert !this.dependsNoact;
		this.dependsAnyact = true;
	}

	@Override
	public void clearDependsEvents() {
		this.dependsEvents.clear();
	}
}
