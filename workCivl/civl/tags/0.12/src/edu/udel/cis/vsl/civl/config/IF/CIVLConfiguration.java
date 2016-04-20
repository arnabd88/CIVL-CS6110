package edu.udel.cis.vsl.civl.config.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.gmc.GMCConfiguration;

public class CIVLConfiguration {
	private boolean debug = false;
	private boolean enablePrintf = true;
	// private int errorBound = 1;
	// private boolean needsInputFileLength = false;
	private boolean saveStates = true;
	private boolean showAmpleSet = false;
	private boolean showAmpleSetWtStates = false;
	private boolean showSavedStates = false;
	private boolean showStates = false;
	private boolean showTransitions = false;
	private boolean simplify = true;
	private boolean statelessPrintf = true;
	private boolean verbose = false;
	private boolean svcomp = false;
	private boolean showProgram = false;
	private String deadlock;
	private PrintStream out;
	private PrintStream err;
	private boolean showPathConditon = false;

	public CIVLConfiguration(GMCConfiguration config) {
		this.debug = config.isTrue(CIVLConstants.debugO);
		this.enablePrintf = config.isTrue(CIVLConstants.enablePrintfO);
		this.saveStates = config.isTrue(CIVLConstants.saveStatesO);
		this.showAmpleSet = config.isTrue(CIVLConstants.showAmpleSetO);
		this.showAmpleSetWtStates = config
				.isTrue(CIVLConstants.showAmpleSetWtStatesO);
		this.showSavedStates = config.isTrue(CIVLConstants.showSavedStatesO);
		this.showStates = config.isTrue(CIVLConstants.showStatesO);
		this.showTransitions = config.isTrue(CIVLConstants.showTransitionsO);
		this.simplify = config.isTrue(CIVLConstants.simplifyO);
		this.statelessPrintf = config.isTrue(CIVLConstants.statelessPrintfO);
		this.verbose = config.isTrue(CIVLConstants.verboseO);
		this.svcomp = config.isTrue(CIVLConstants.svcompO);
		this.deadlock = (String) config.getValue(CIVLConstants.deadlockO);
		this.setShowProgram(config.isTrue(CIVLConstants.showProgramO));
		this.showPathConditon = config.isTrue(CIVLConstants.showPathConditionO);
	}

	public CIVLConfiguration() {
		// TODO Auto-generated constructor stub
	}

	public void setOut(PrintStream out) {
		this.out = out;
	}

	public void setErr(PrintStream err) {
		this.err = err;
	}

	public void setDebug(boolean debug) {
		this.debug = debug;
	}

	public void setEnablePrintf(boolean enablePrintf) {
		this.enablePrintf = enablePrintf;
	}

	public void setSaveStates(boolean saveStates) {
		this.saveStates = saveStates;
	}

	public void setShowAmpleSet(boolean showAmpleSet) {
		this.showAmpleSet = showAmpleSet;
	}

	public void setShowAmpleSetWtStates(boolean showAmpleSetWtStates) {
		this.showAmpleSetWtStates = showAmpleSetWtStates;
	}

	public void setShowSavedStates(boolean showSavedStates) {
		this.showSavedStates = showSavedStates;
	}

	public void setShowStates(boolean showStates) {
		this.showStates = showStates;
	}

	public void setShowTransitions(boolean showTransitions) {
		this.showTransitions = showTransitions;
	}

	public void setSimplify(boolean simplify) {
		this.simplify = simplify;
	}

	public void setStatelessPrintf(boolean statelessPrintf) {
		this.statelessPrintf = statelessPrintf;
	}

	public void setVerbose(boolean verbose) {
		this.verbose = verbose;
	}

	public boolean debug() {
		return debug;
	}

	public boolean verbose() {
		return verbose;
	}

	public boolean debugOrVerbose() {
		return debug || verbose;
	}

	public boolean enablePrintf() {
		return this.enablePrintf;
	}

	public boolean saveStates() {
		return this.saveStates;
	}

	public boolean showAmpleSet() {
		return this.showAmpleSet;
	}

	public boolean showAmpleSetWtStates() {
		return this.showAmpleSetWtStates;
	}

	public boolean showSavedStates() {
		return this.showSavedStates;
	}

	public boolean showStates() {
		return this.showStates;
	}

	public boolean showTransitions() {
		return this.showTransitions;
	}

	public boolean simplify() {
		return this.simplify;
	}

	public boolean statelessPrintf() {
		return this.statelessPrintf;
	}

	public PrintStream out() {
		return this.out;
	}

	public PrintStream err() {
		return this.err;
	}

	public boolean printTransitions() {
		return this.showTransitions || this.verbose || this.debug;
	}

	public boolean printStates() {
		return this.showStates || this.verbose || this.debug;
	}

	public boolean svcomp() {
		return svcomp;
	}

	public void setSvcomp(boolean svcomp) {
		this.svcomp = svcomp;
	}

	public String deadlock() {
		return deadlock;
	}

	public void setDeadlock(String deadlock) {
		this.deadlock = deadlock;
	}

	public boolean showProgram() {
		return showProgram;
	}

	public void setShowProgram(boolean showProgram) {
		this.showProgram = showProgram;
	}

	public boolean showPathConditon() {
		return showPathConditon;
	}

	public void setShowPathConditon(boolean showPathConditon) {
		this.showPathConditon = showPathConditon;
	}

}
