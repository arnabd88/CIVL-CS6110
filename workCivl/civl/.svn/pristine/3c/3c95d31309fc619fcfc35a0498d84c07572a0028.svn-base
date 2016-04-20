package edu.udel.cis.vsl.civl.kripke;

import java.io.PrintStream;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Random;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.state.Process;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.state.StateFactoryIF;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionFactory;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

public class Enabler implements
		EnablerIF<State, Transition, TransitionSequence> {

	private ModelFactory modelFactory;

	private TransitionFactory transitionFactory;

	private StateFactoryIF stateFactory;

	private boolean debugging = false;

	private PrintStream debugOut = System.out;

	private SymbolicUniverse universe;

	private Evaluator evaluator;

	private Executor executor;

	private long enabledTransitionSets = 0;

	private long ampleSets = 0;

	private BooleanExpression falseValue;

	private boolean randomMode = false;

	private Random generator = null;

	public Enabler(TransitionFactory transitionFactory, Evaluator evaluator,
			Executor executor) {
		this.transitionFactory = transitionFactory;
		this.evaluator = evaluator;
		this.executor = executor;
		this.modelFactory = evaluator.modelFactory();
		this.stateFactory = evaluator.stateFactory();
		this.universe = modelFactory.universe();
		this.falseValue = universe.falseExpression();
	}

	public Enabler(TransitionFactory transitionFactory, Evaluator evaluator,
			Executor executor, boolean randomMode, Random generator) {
		this(transitionFactory, evaluator, executor);
		this.randomMode = randomMode;
		this.generator = generator;
	}

	@Override
	public boolean debugging() {
		return debugging;
	}

	@Override
	public TransitionSequence enabledTransitions(State state) {
		TransitionSequence transitions;

		if (state.pathCondition().isFalse())
			// return empty set of transitions:
			return new TransitionSequence(state);
		if (debugging && enabledTransitionSets % 1000 == 0) {
			System.out.println("Ample transition sets: " + ampleSets + "/"
					+ enabledTransitionSets);
		}
		transitions = enabledTransitionsPOR(state);
		if (randomMode && transitions.size() > 0) {
			TransitionSequence singletonSequence = new TransitionSequence(state);
			singletonSequence.add(transitions.get(generator.nextInt(transitions
					.size())));
			return singletonSequence;
		}
		return transitions;
	}

	// /**
	// * Attempts to form an ample set from the enabled transitions of the given
	// * process, from the given state. If this is not possible, returns all
	// * transitions.
	// */
	// private TransitionSequence enabledTransitionsPOR(State state) {
	// TransitionSequence transitions = transitionFactory
	// .newTransitionSequence(state);
	// Process[] processStates = state.processes();
	//
	// enabledTransitionSets++;
	// for (Process p : processStates) {
	// TransitionSequence localTransitions = transitionFactory
	// .newTransitionSequence(state);
	// boolean allLocal = true;
	//
	// // A process with an empty stack has no current location.
	// if (p == null || p.hasEmptyStack()) {
	// continue;
	// }
	// for (Statement s : p.location().outgoing()) {
	// BooleanExpression newPathCondition = newPathCondition(state,
	// p.id(), s);
	// int statementScope = p.scope();
	//
	// if (s.statementScope() != null) {
	// while (!state.getScope(statementScope).lexicalScope()
	// .equals(s.statementScope())) {
	// statementScope = state.getParentId(statementScope);
	// }
	// }
	// if (state.getScope(statementScope).numberOfReachers() > 1) {
	// allLocal = false;
	// }
	// if (!newPathCondition.isFalse()) {
	// try {
	// if (s instanceof ChooseStatement) {
	// Evaluation eval = evaluator.evaluate(stateFactory
	// .setPathCondition(state, newPathCondition),
	// p.id(), ((ChooseStatement) s).rhs());
	// IntegerNumber upperNumber = (IntegerNumber) universe
	// .reasoner(eval.state.pathCondition())
	// .extractNumber(
	// (NumericExpression) eval.value);
	// int upper;
	//
	// if (upperNumber == null)
	// throw new CIVLStateException(
	// ErrorKind.INTERNAL, Certainty.NONE,
	// "Argument to $choose_int not concrete: "
	// + eval.value, eval.state,
	// s.getSource());
	// upper = upperNumber.intValue();
	// for (int i = 0; i < upper; i++) {
	// localTransitions
	// .add(transitionFactory
	// .newChooseTransition(eval.state
	// .pathCondition(), p
	// .id(), s, universe
	// .integer(i)));
	// }
	// continue;
	// } else if (s instanceof WaitStatement) {
	// Evaluation eval = evaluator.evaluate(stateFactory
	// .setPathCondition(state, newPathCondition),
	// p.id(), ((WaitStatement) s).process());
	// int pidValue = modelFactory.getProcessId(
	// ((WaitStatement) s).process().getSource(),
	// eval.value);
	//
	// if (pidValue < 0) {
	// CIVLExecutionException e = new CIVLStateException(
	// ErrorKind.INVALID_PID,
	// Certainty.PROVEABLE,
	// "Unable to call $wait on a process that has already been the target of a $wait.",
	// state, s.getSource());
	//
	// evaluator.log().report(e);
	// // TODO: recover: add a no-op transition
	// throw e;
	// }
	// if (!state.process(pidValue).hasEmptyStack()) {
	// continue;
	// }
	// }
	// localTransitions.add(transitionFactory
	// .newSimpleTransition(newPathCondition, p.id(),
	// s));
	// } catch (UnsatisfiablePathConditionException e) {
	// // nothing to do: don't add this transition
	// }
	// }
	// }
	// if (allLocal && localTransitions.size() > 0) {
	// ampleSets++;
	// return localTransitions;
	// } else {
	// transitions.addAll(localTransitions);
	// }
	// }
	// return transitions;
	// }

	/**
	 * Attempts to form an ample set from the enabled transitions of the given
	 * process, from the given state. If this is not possible, returns all
	 * transitions.
	 */
	private TransitionSequence enabledTransitionsPOR(State state) {
		TransitionSequence transitions = transitionFactory
				.newTransitionSequence(state);
		Process[] processStates = state.processes();
		Map<Process, TransitionSequence> processTransitions = new LinkedHashMap<Process, TransitionSequence>();
		int totalTransitions = 0;

		enabledTransitionSets++;
		for (Process p : processStates) {
			TransitionSequence localTransitions = transitionFactory
					.newTransitionSequence(state);
			boolean allLocal = true;

			// A process with an empty stack has no current location.
			if (p == null || p.hasEmptyStack()) {
				continue;
			}
			for (Statement s : p.location().outgoing()) {
				BooleanExpression newPathCondition = newPathCondition(state,
						p.id(), s);
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
				if (!newPathCondition.isFalse()) {
					try {
						if (s instanceof ChooseStatement) {
							Evaluation eval = evaluator.evaluate(stateFactory
									.setPathCondition(state, newPathCondition),
									p.id(), ((ChooseStatement) s).rhs());
							IntegerNumber upperNumber = (IntegerNumber) universe
									.reasoner(eval.state.pathCondition())
									.extractNumber(
											(NumericExpression) eval.value);
							int upper;

							if (upperNumber == null)
								throw new CIVLStateException(
										ErrorKind.INTERNAL, Certainty.NONE,
										"Argument to $choose_int not concrete: "
												+ eval.value, eval.state,
										s.getSource());
							upper = upperNumber.intValue();
							for (int i = 0; i < upper; i++) {
								localTransitions
										.add(transitionFactory
												.newChooseTransition(eval.state
														.pathCondition(), p
														.id(), s, universe
														.integer(i)));
							}
							continue;
						} else if (s instanceof WaitStatement) {
							Evaluation eval = evaluator.evaluate(stateFactory
									.setPathCondition(state, newPathCondition),
									p.id(), ((WaitStatement) s).process());
							int pidValue = modelFactory.getProcessId(
									((WaitStatement) s).process().getSource(),
									eval.value);

							if (pidValue < 0) {
								CIVLExecutionException e = new CIVLStateException(
										ErrorKind.INVALID_PID,
										Certainty.PROVEABLE,
										"Unable to call $wait on a process that has already been the target of a $wait.",
										state, s.getSource());

								evaluator.log().report(e);
								// TODO: recover: add a no-op transition
								throw e;
							}
							if (!state.process(pidValue).hasEmptyStack()) {
								continue;
							}
						}
						localTransitions.add(transitionFactory
								.newSimpleTransition(newPathCondition, p.id(),
										s));
					} catch (UnsatisfiablePathConditionException e) {
						// nothing to do: don't add this transition
					}
				}
			}
			totalTransitions += localTransitions.size();
			if (allLocal && localTransitions.size() > 0) {
				ampleSets++;
				processTransitions.put(p, localTransitions);
				if (localTransitions.size() == 1) {
					// If the size isn't 1, keep looking for a smaller local
					// set.
					return localTransitions;
				}
			} else {
				transitions.addAll(localTransitions);
			}
		}
		if (processTransitions.size() > 0) {
			Process smallestProcess = null;
			int smallestProcessSetSize = totalTransitions + 1;

			for (Process p : processTransitions.keySet()) {
				if (processTransitions.get(p).size() < smallestProcessSetSize) {
					smallestProcess = p;
					smallestProcessSetSize = processTransitions.get(p).size();
				}
			}
			assert smallestProcess != null;
			// System.out.println("Returning " + smallestProcessSetSize +
			// " transitions for 1 process");
			return processTransitions.get(smallestProcess);
		}
		// System.out.println("Returning " + totalTransitions + " transitions");
		return transitions;
	}

	/**
	 * Given a state, a process, and a statement, check if the statement's guard
	 * is satisfiable under the path condition. If it is, return the conjunction
	 * of the path condition and the guard. This will be the new path condition.
	 * Otherwise, return false.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The id of the currently executing process.
	 * @param statement
	 *            The statement.
	 * @return The new path condition. False if the guard is not satisfiable
	 *         under the path condition.
	 */
	private BooleanExpression newPathCondition(State state, int pid,
			Statement statement) {
		try {
			Evaluation eval = evaluator.evaluate(state, pid, statement.guard());
			BooleanExpression pathCondition = eval.state.pathCondition();
			BooleanExpression guard = (BooleanExpression) eval.value;
			Reasoner reasoner = universe.reasoner(pathCondition);

//			if (statement instanceof CallOrSpawnStatement) {
//				if (((CallOrSpawnStatement) statement).function() instanceof SystemFunction) {
//					LibraryExecutor libraryExecutor = executor
//							.libraryExecutor((CallOrSpawnStatement) statement);
//					guard = universe.and(guard,
//							libraryExecutor.getGuard(state, pid, statement));
//				}
//			}
			// System.out.println("Enabler.newPathCondition() : Process " + pid
			// + " is at " + state.process(pid).peekStack().location());
			if (reasoner.isValid(guard))
				return pathCondition;
			if (reasoner.isValid(universe.not(guard)))
				return falseValue;
			return universe.and(pathCondition, guard);
		} catch (UnsatisfiablePathConditionException e) {
			return falseValue;
		}
	}

	@Override
	public PrintStream getDebugOut() {
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
	public void print(PrintStream out, TransitionSequence transitionSequence) {
		// TODO Auto-generated method stub

	}

	@Override
	public void printFirstTransition(PrintStream arg0, TransitionSequence arg1) {
		// TODO Auto-generated method stub

	}

	@Override
	public void printRemaining(PrintStream arg0, TransitionSequence arg1) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setDebugOut(PrintStream debugOut) {
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
