package edu.udel.cis.vsl.civl.log.IF;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.gmc.ExcessiveErrorException;
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
public class CIVLErrorLogger extends ErrorLog {

	private GMCConfiguration config;

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

	public CIVLErrorLogger(File directory, String sessionName, PrintStream out,
			GMCConfiguration config, SymbolicUniverse universe, boolean solve) {
		super(directory, sessionName, out);
		this.config = config;
		this.universe = universe;
		this.trueReasoner = universe.reasoner(universe.trueExpression());
		this.solve = solve;
	}

	/**
	 * <p>
	 * Report a (possible) error detected in the course of evaluating an
	 * expression. This is the method that should normally be used for logging
	 * and reporting errors.
	 * </p>
	 * 
	 * <p>
	 * This is the general protocol for checking conditions and reporting and
	 * recovering from errors: first, check some condition holds and call the
	 * result of that check "condsat", which may be YES, NO, or MAYBE. If
	 * condsat is YES, proceed. Otherwise, there is a problem and you should
	 * call this method.
	 * </p>
	 * 
	 * <p>
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
	 * </p>
	 * 
	 * <p>
	 * Returns the state obtained by adding the claim to the pc of the given
	 * state.
	 * </p>
	 * 
	 * @param source
	 *            the source of the expression being evaluated
	 * @param state
	 *            the state in which the evaluation is taking place
	 * @param process
	 *            a string representation of the process that is evaluating the
	 *            expression; used for reporting errors
	 * @param stateString
	 *            a string representation of the state which is used in
	 *            CIVLExecutionException that is recorded in the log
	 * @param claim
	 *            the boolean expression which was expected to hold. This should
	 *            already have been checked for validity before invoking this
	 *            method. The result of that check should not have been "YES"
	 *            (i.e., definitely valid); that is why you are calling this
	 *            method
	 * @param resultType
	 *            the result of evaluating the validity of the claim (which you
	 *            did before you called this method).
	 * @param errorKind
	 *            the kind of error you want to report if it turns out there is
	 *            an error
	 * @param message
	 *            the message you want to include in the error report if it
	 *            turns out there is an error
	 * @throws UnsatisfiablePathConditionException
	 *             if it turns out the path condition is unsatisfiable; in this
	 *             case no error will be reported since the current path is
	 *             infeasible
	 * @return
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

		assert resultType != ResultType.YES;
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
	 * @throws ExcessiveErrorException
	 *             if the number of errors reported has exceeded the specified
	 *             bound
	 */
	public void reportError(CIVLExecutionException err) {
		try {
			report(new CIVLLogEntry(config, err));
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
