package edu.udel.cis.vsl.civl.library;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.library.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.common.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.transition.SimpleTransition;
import edu.udel.cis.vsl.civl.transition.TransitionFactory;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class implements the common logic of library enablers.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class CommonLibraryEnabler extends Library implements
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

	// /**
	// * The symbolic expression of one.
	// */
	// protected NumericExpression one;
	//
	// /**
	// * The symbolic object of integer one.
	// */
	// protected IntObject oneObject;

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

	/**
	 * The unique transition factory used by the system.
	 */
	protected TransitionFactory transitionFactory;

	// /**
	// * The symbolic universe for symbolic computations.
	// */
	// protected SymbolicUniverse universe;
	//
	// /**
	// * The symbolic expression of zero.
	// */
	// protected NumericExpression zero;
	//
	// /**
	// * The symbolic object of integer zero.
	// */
	// protected IntObject zeroObject;

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
	protected CommonLibraryEnabler(Enabler primaryEnabler, PrintStream output,
			ModelFactory modelFactory) {
		super(primaryEnabler.evaluator().universe());
		this.primaryEnabler = primaryEnabler;
		this.transitionFactory = primaryEnabler.transitionFactory();
		this.evaluator = primaryEnabler.evaluator();
		this.stateFactory = evaluator.stateFactory();
		this.output = output;
		this.modelFactory = modelFactory;
	}

	/* ********************* Methods from LibraryEnabler ******************* */

	@Override
	public Evaluation evaluateGuard(CIVLSource source, State state, int pid,
			String function, List<Expression> arguments) {
		return new Evaluation(state, universe.trueExpression());
	}

	@Override
	public Set<Integer> ampleSet(State state, int pid,
			CallOrSpawnStatement statement,
			Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap) {
		return new HashSet<>();
	}

	@Override
	public ArrayList<SimpleTransition> enabledTransitions(State state,
			CallOrSpawnStatement call, BooleanExpression pathCondition,
			int pid, int processIdentifier, Statement assignAtomicLock) {
		Statement transitionStatement;
		ArrayList<SimpleTransition> localTransitions = new ArrayList<>();

		if (assignAtomicLock != null) {
			StatementList statementList = new StatementList(assignAtomicLock);

			statementList.add(call);
			transitionStatement = statementList;
		} else {
			transitionStatement = call;
		}
		localTransitions.add(transitionFactory.newSimpleTransition(
				pathCondition, pid, processIdentifier, transitionStatement));
		return localTransitions;
	}

}
