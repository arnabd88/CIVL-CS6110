package edu.udel.cis.vsl.civl.model.common.contract;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.NamedFunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

public class CommonNamedFunctionBehavior extends CommonFunctionBehavior
		implements NamedFunctionBehavior {
	private String name;
	private Set<Expression> assumptions = new HashSet<>();

	public CommonNamedFunctionBehavior(CIVLSource source, String name) {
		super(source);
		this.name = name;
	}

	@Override
	public String name() {
		return this.name;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean isDebug) {
		String subPrefix = prefix + "| ";

		out.println(prefix + "behavior " + this.name + ":");
		if (this.numAssumptions() > 0) {
			boolean first = true;

			out.print(subPrefix + "assumes ");
			for (Expression expr : this.assumptions) {
				if (!first)
					out.print(" && ");
				else
					first = false;
				out.print(expr.toString());
			}
			out.println();
		}
		super.print(subPrefix, out, isDebug);
	}

	@Override
	public Iterable<Expression> assumptions() {
		return this.assumptions;
	}

	@Override
	public void addAssumption(Expression assumption) {
		this.assumptions.add(assumption);
	}

	@Override
	public int numAssumptions() {
		return this.assumptions.size();
	}

}
