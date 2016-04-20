package edu.udel.cis.vsl.civl.run.common;

import edu.udel.cis.vsl.civl.run.IF.CommandLine;

public class CompareCommandLine extends BaseCommandLine implements CommandLine {

	/**
	 * 
	 */
	private static final long serialVersionUID = -7987487073665135306L;

	/**
	 * The name of the specification section of the command line
	 */
	public final static String SPEC = "spec";

	/**
	 * The name of the specification section of the command line
	 */
	public final static String IMPL = "impl";

	private NormalCommandLine specification;

	private NormalCommandLine implementation;

	private boolean isReplay;

	// public CompareCommandLine(NormalCommandLine spec, NormalCommandLine impl)
	// {
	// this.specification = spec;
	// this.implementation = impl;
	// }

	public CompareCommandLine(boolean isReplay) {
		this.specification = new NormalCommandLine();
		this.implementation = new NormalCommandLine();
		this.setReplay(isReplay);
	}

	public void setSpecification(NormalCommandLine spec) {
		this.specification = spec;
	}

	public void setImplemenation(NormalCommandLine impl) {
		this.implementation = impl;
	}

	public NormalCommandLine specification() {
		return this.specification;
	}

	public NormalCommandLine implementation() {
		return this.implementation;
	}

	@Override
	public CommandLineKind commandLineKind() {
		return CommandLineKind.COMPARE;
	}

	public boolean isReplay() {
		return isReplay;
	}

	public void setReplay(boolean isReplay) {
		this.isReplay = isReplay;
	}
}
