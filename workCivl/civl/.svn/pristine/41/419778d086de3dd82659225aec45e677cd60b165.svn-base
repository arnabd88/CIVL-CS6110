package edu.udel.cis.vsl.civl.library.IF;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class provides the common data and operations of library enablers.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class BaseLibraryEnabler extends Library implements
		LibraryEnabler {

	/* *************************** Instance Fields ************************* */

	/**
	 * The evaluator for evaluating expressions.
	 */
	protected Evaluator evaluator;

	/**
	 * The model factory of the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The output stream to be used for printing.
	 */
	protected PrintStream output = System.out;

	/**
	 * The enabler for normal CIVL execution.
	 */
	protected Enabler primaryEnabler;

	/**
	 * The state factory for state-related computation.
	 */
	protected StateFactory stateFactory;

	/* ***************************** Constructor *************************** */

	/**
	 * Creates a new instance of library enabler.
	 * 
	 * @param primaryEnabler
	 *            The enabler for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param modelFactory
	 *            The model factory of the system.
	 */
	public BaseLibraryEnabler(String name, Enabler primaryEnabler,
			Evaluator evaluator, PrintStream output, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil) {
		super(name, evaluator.universe(), symbolicUtil);
		this.primaryEnabler = primaryEnabler;
		this.evaluator = evaluator;
		this.stateFactory = evaluator.stateFactory();
		this.output = output;
		this.modelFactory = modelFactory;
	}

	/* ********************* Methods from LibraryEnabler ******************* */

	@Override
	public Set<Integer> ampleSet(State state, int pid,
			CallOrSpawnStatement statement,
			Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap) {
		return new HashSet<>();
	}

	@Override
	public List<Transition> enabledTransitions(State state,
			CallOrSpawnStatement call, BooleanExpression pathCondition,
			int pid, int processIdentifier, Statement assignAtomicLock)
			throws UnsatisfiablePathConditionException {
		Statement transitionStatement;
		List<Transition> localTransitions = new LinkedList<>();

		if (assignAtomicLock != null) {
			StatementList statementList = modelFactory
					.statmentList(assignAtomicLock);

			statementList.add(call);
			transitionStatement = statementList;
		} else {
			transitionStatement = call;
		}
		localTransitions.add(Semantics.newTransition(pathCondition, pid,
				processIdentifier, transitionStatement));
		return localTransitions;
	}

}
