/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;

/**
 * A wait statement, to wait for another process to complete.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonWaitStatement extends CommonStatement implements
		WaitStatement {

	private Expression process;

	/**
	 * A join statement, to wait for another process to complete.
	 * 
	 * @param source
	 *            The source location for this join.
	 * @param process
	 *            A reference to the process.
	 */
	public CommonWaitStatement(CIVLSource civlSource, Location source,
			Expression process) {
		super(civlSource, source);
		this.process = process;
	}

	/**
	 * @return The process.
	 */
	@Override
	public Expression process() {
		return process;
	}

	/**
	 * @param process
	 *            The process.
	 */
	@Override
	public void setProcess(Expression process) {
		this.process = process;
	}

	@Override
	public String toString() {
		return "wait " + process;
	}
	
	@Override
	public void caculateDerefs() {
		this.process.calculateDerefs();
		this.hasDerefs = this.process.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.process.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		this.guard().purelyLocalAnalysis();
		this.process.purelyLocalAnalysis();
		this.purelyLocal = this.guard().isPurelyLocal() 
				&& this.process.isPurelyLocal();
	}

}
