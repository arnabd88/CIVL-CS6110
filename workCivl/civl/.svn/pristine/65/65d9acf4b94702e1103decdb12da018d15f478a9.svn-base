package edu.udel.cis.vsl.civl.kripke;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;

import edu.udel.cis.vsl.civl.log.ExecutionException;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.JoinStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.state.Process;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionFactory;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.civl.util.ExecutionProblem.Certainty;
import edu.udel.cis.vsl.civl.util.ExecutionProblem.ErrorKind;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;

public class Enabler implements
		EnablerIF<State, Transition, TransitionSequence> {

	private TransitionFactory transitionFactory;
	private boolean debugging = false;
	private PrintWriter debugOut = new PrintWriter(System.out);
	private SymbolicUniverse universe;
	private Evaluator evaluator;
	private long enabledTransitionSets = 0;
	private long ampleSets = 0;
	private String pidPrefix = "PID_";

	public Enabler(TransitionFactory transitionFactory,
			SymbolicUniverse universe, Evaluator evaluator) {
		this.transitionFactory = transitionFactory;
		this.evaluator = evaluator;
		this.universe = universe;
	}

	@Override
	public boolean debugging() {
		return debugging;
	}

	@Override
	public TransitionSequence enabledTransitions(State state) {
		if (debugging && enabledTransitionSets % 1000 == 0) {
			System.out.println("Ample transition sets: " + ampleSets + "/"
					+ enabledTransitionSets);
		}
		return enabledTransitionsPOR(state);
	}

	/**
	 * Attempts to form an ample set from the enabled transitions of the given
	 * process, from the given state. If this is not possible, returns all
	 * transitions.
	 */
	private TransitionSequence enabledTransitionsPOR(State state) {
		TransitionSequence transitions = transitionFactory
				.newTransitionSequence(state);

		enabledTransitionSets++;
		for (Process p : state.processes()) {
			TransitionSequence localTransitions = transitionFactory
					.newTransitionSequence(state);
			boolean allLocal = true;

			// A process with an empty stack has no current location.
			if (p == null || p.hasEmptyStack()) {
				continue;
			}
			for (Statement s : p.location().outgoing()) {
				SymbolicExpression newPathCondition = newPathCondition(state,
						p.id(), state.pathCondition(), s);
				int statementScope = p.scope();

				if (s.statementScope() != null) {
					while (!state.getScope(statementScope).lexicalScope()
							.equals(s.statementScope())) {
						statementScope = state.getParentId(statementScope);
					}
				}
				if (state.getScope(statementScope).numberOfReachers() > 1) {
					allLocal = false;
				}
				if (newPathCondition != null) {
					if (s instanceof ChooseStatement) {
						SymbolicExpression argument = evaluator.evaluate(state,
								p.id(), ((ChooseStatement) s).rhs());
						Integer upper = extractInt(universe.reasoner(
								(BooleanExpression) newPathCondition).simplify(
								argument));

						for (int i = 0; i < upper.intValue(); i++) {
							localTransitions.add(transitionFactory
									.newChooseTransition(newPathCondition,
											p.id(), s, universe.integer(i)));
						}
						continue;
					} else if (s instanceof JoinStatement) {
						SymbolicExpression pidExpression = evaluator.evaluate(
								state, p.id(), ((JoinStatement) s).process());
						int pidValue;

						if (!(pidExpression instanceof SymbolicConstant)) {
							ByteArrayOutputStream baos = new ByteArrayOutputStream();
							PrintStream ps = new PrintStream(baos);

							state.print(ps);
							evaluator
									.log()
									.report(new ExecutionException(
											ErrorKind.INVALID_PID,
											Certainty.PROVEABLE,
											"Unknown process ID in: " + s
													+ "\n\n" + baos.toString()));
							continue;
						}
						assert pidExpression instanceof SymbolicConstant;
						assert ((SymbolicConstant) pidExpression).name()
								.getString().startsWith(pidPrefix);
						// TODO: Throw exception if not the right type.
						pidValue = Integer
								.parseInt(((SymbolicConstant) pidExpression)
										.name().getString()
										.substring(pidPrefix.length()));
						if (pidValue == -1) {
							ByteArrayOutputStream baos = new ByteArrayOutputStream();
							PrintStream ps = new PrintStream(baos);

							state.print(ps);
							evaluator
									.log()
									.report(new ExecutionException(
											ErrorKind.INVALID_PID,
											Certainty.PROVEABLE,
											"Unable to call $wait on a process that has already been the target of a $wait.  At "
													+ s.source()
													+ " : "
													+ s
													+ "\n\n" + baos.toString()));
							continue;
						}
						if (!state.process(pidValue).hasEmptyStack()) {
							continue;
						}
					}
					localTransitions.add(transitionFactory.newSimpleTransition(
							newPathCondition, p.id(), s));
				}
			}
			if (allLocal && localTransitions.size() > 0) {
				ampleSets++;
				return localTransitions;
			} else {
				transitions.addAll(localTransitions);
			}
		}
		return transitions;
	}

	/**
	 * 
	 * @param expression
	 *            A symbolic expression.
	 * @return A concrete integer if one can be extracted. Else null.
	 */
	private Integer extractInt(SymbolicExpression expression) {
		Number number = universe.extractNumber((NumericExpression) expression);
		Integer intValue;

		assert number instanceof IntegerNumber;
		intValue = ((IntegerNumber) number).intValue();
		return intValue;
	}

	/**
	 * Given a state, a process, a path condition, and a statement, check if the
	 * statement's guard is satisfiable under the path condition. If it is,
	 * return the conjunction of the path condition and the guard. This will be
	 * the new path condition. Otherwise, return null.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The id of the currently executing process.
	 * @param pathCondition
	 *            The path condition.
	 * @param statement
	 *            The statement.
	 * @return The new path condition. Null if the guard is not satisfiable
	 *         under the path condition.
	 */
	private SymbolicExpression newPathCondition(State state, int pid,
			SymbolicExpression pathCondition, Statement statement) {
		SymbolicExpression newPathCondition = null;
		SymbolicExpression guard = evaluator.evaluate(state, pid,
				statement.guard());
		Reasoner reasoner = universe
				.reasoner(((BooleanExpression) pathCondition));
		ValidityResult result = reasoner.valid((BooleanExpression) guard);
		ValidityResult negResult = reasoner.valid(universe
				.not((BooleanExpression) guard));

		// System.out.println("Enabler.newPathCondition() : Process " + pid
		// + " is at " + state.process(pid).peekStack().location());
		if (result.getResultType() == ResultType.YES) {
			newPathCondition = pathCondition;
		} else if (negResult.getResultType() == ResultType.YES) {
			return null;
		} else {
			newPathCondition = universe.and((BooleanExpression) pathCondition,
					(BooleanExpression) guard);
		}
		return newPathCondition;
	}

	@Override
	public PrintWriter getDebugOut() {
		return debugOut;
	}

	@Override
	public boolean hasNext(TransitionSequence transitionSequence) {
		return !transitionSequence.isEmpty();
	}

	@Override
	public Transition next(TransitionSequence transitionSequence) {
		return transitionSequence.remove();
	}

	@Override
	public Transition peek(TransitionSequence transitionSequence) {
		return transitionSequence.peek();
	}

	@Override
	public void print(PrintWriter out, TransitionSequence transitionSequence) {
		// TODO Auto-generated method stub

	}

	@Override
	public void printFirstTransition(PrintWriter arg0, TransitionSequence arg1) {
		// TODO Auto-generated method stub

	}

	@Override
	public void printRemaining(PrintWriter arg0, TransitionSequence arg1) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setDebugOut(PrintWriter debugOut) {
		this.debugOut = debugOut;
	}

	@Override
	public void setDebugging(boolean debugging) {
		this.debugging = debugging;
	}

	@Override
	public State source(TransitionSequence transitionSequence) {
		return transitionSequence.state();
	}

}
