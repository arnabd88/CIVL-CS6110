package edu.udel.cis.vsl.civl.log.IF;

import java.io.FileNotFoundException;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.ModelResult;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * CIVLErrorLogger logs all errors of the system.
 * 
 * @author Manchun Zheng
 * 
 */
public class CIVLErrorLogger {

	private GMCConfiguration config;

	/**
	 * The error logging facility.
	 */
	private ErrorLog log;

	/**
	 * The unique symbolic universe used in the system.
	 */
	private SymbolicUniverse universe;

	/**
	 * Reasoner with trivial context "true". Used to determine satisfiability of
	 * path conditions.
	 */
	private Reasoner trueReasoner;

	/**
	 * Solve for concrete counterexamples?
	 */
	private boolean solve = false;

	public CIVLErrorLogger(GMCConfiguration config, ErrorLog log,
			SymbolicUniverse universe, boolean solve) {
		this.log = log;
		this.config = config;
		this.universe = universe;
		this.trueReasoner = universe.reasoner(universe.trueExpression());
		this.solve = solve;
	}

	/**
	 * Report a (possible) error detected in the course of evaluating an
	 * expression.
	 * 
	 * Protocol for checking conditions and reporting and recovering from
	 * errors. First, check some condition holds and call the result of that
	 * check "condsat", which may be YES, NO, or MAYBE. If condsat is YES,
	 * proceed. Otherwise, there is a problem: call this method.
	 * 
	 * This method first checks the satisfiability of the path condition, call
	 * the result "pcsat". Logs a violation with certainty determined as
	 * follows:
	 * <ul>
	 * <li>pcsat=YES && condsat=NO : certainty=PROVEABLE</li>
	 * <li>pcsat=YES && condsat=MAYBE : certainty=MAYBE</li>
	 * <li>pcsat=MAYBE && condsat=NO : certainty=MAYBE</li>
	 * <li>pcsat=MAYBE && condsat=MAYBE : certainty=MAYBE</li>
	 * <li>pcsat=NO: no error to report</li>
	 * </ul>
	 * 
	 * Returns the state obtained by adding the claim to the pc of the given
	 * state.
	 * 
	 * TODO: move this to its own package, like log, make public
	 * 
	 */
	public State logError(CIVLSource source, State state, String process,
			StringBuffer stateString, BooleanExpression claim,
			ResultType resultType, ErrorKind errorKind, String message)
			throws UnsatisfiablePathConditionException {
		BooleanExpression pc = state.getPathCondition(), newPc;
		BooleanExpression npc = universe.not(pc);
		ValidityResult validityResult = trueReasoner.valid(npc);
		ResultType nsat = validityResult.getResultType();
		Certainty certainty;
		CIVLExecutionException error;

		// performance! need to cache the satisfiability of each pc somewhere
		// negation is slow
		// maybe add "nsat" to Reasoner.
		if (nsat == ResultType.YES)
			// no error to report---an infeasible path
			throw new UnsatisfiablePathConditionException();
		if (nsat == ResultType.MAYBE)
			certainty = Certainty.MAYBE;
		else { // pc is definitely satisfiable
			certainty = null;
			if (resultType == ResultType.NO) {
				// need something satisfying PC and not claim...
				if (solve) {
					ValidityResult claimResult = trueReasoner
							.validOrModel(universe.or(npc, claim));

					if (claimResult.getResultType() == ResultType.NO) {
						Map<SymbolicConstant, SymbolicExpression> model = ((ModelResult) claimResult)
								.getModel();

						if (model != null) {
							certainty = Certainty.CONCRETE;
							message += "\nCounterexample:\n" + model + "\n";
						}
					}
				}
				if (certainty == null)
					certainty = Certainty.PROVEABLE;
			} else {
				certainty = Certainty.MAYBE;
			}
		}
		error = new CIVLExecutionException(errorKind, certainty, process,
				message, stateString, source);
		reportError(error);
		newPc = universe.and(pc, claim);
		// need to check satisfiability again because failure to do so
		// could lead to a SARLException when some subsequent evaluation
		// takes place
		nsat = trueReasoner.valid(universe.not(newPc)).getResultType();
		if (nsat == ResultType.YES)
			throw new UnsatisfiablePathConditionException();
		state = state.setPathCondition(newPc);
		return state;
	}

	/**
	 * Writes the given execution exception to the log.
	 * 
	 * @param err
	 *            a CIVL execution exception
	 */
	public void reportError(CIVLExecutionException err) {
		try {
			log.report(new CIVLLogEntry(config, err));
		} catch (FileNotFoundException e) {
			throw new CIVLException(e.toString(), err.getSource());
		}
	}

	/**
	 * Checks whether the path condition is satisfiable and logs an error if it
	 * is (or might be). If the path condition is definitely unsatisfiable,
	 * there is no error to log, and an UnsatisfiablePathConditionException is
	 * thrown.
	 * 
	 * @param source
	 *            source code element used to report the error
	 * @param state
	 *            the current state in which the possible error is detected
	 * @param errorKind
	 *            the kind of error (e.g., DEREFERENCE)
	 * @param message
	 *            the message to include in the error report
	 * @throws UnsatisfiablePathConditionException
	 *             if the path condition is definitely unsatisfiable
	 */
	public void logSimpleError(CIVLSource source, State state, String process,
			StringBuffer stateString, ErrorKind errorKind, String message)
			throws UnsatisfiablePathConditionException {
		BooleanExpression pc = state.getPathCondition();
		BooleanExpression npc = universe.not(pc);
		ValidityResult validityResult = trueReasoner.valid(npc);
		ResultType nsat = validityResult.getResultType();
		Certainty certainty;
		CIVLExecutionException error;

		// performance! need to cache the satisfiability of each pc somewhere
		// negation is slow
		// maybe add "nsat" to Reasoner.
		if (nsat == ResultType.YES)
			// no error to report---an infeasible path
			throw new UnsatisfiablePathConditionException();
		if (nsat == ResultType.MAYBE)
			certainty = Certainty.MAYBE;
		else { // pc is definitely satisfiable
			certainty = Certainty.PROVEABLE;
		}
		error = new CIVLExecutionException(errorKind, certainty, process,
				message, stateString, source);
		reportError(error);
	}
}
