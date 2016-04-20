package edu.udel.cis.vsl.civl.library.comm;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

public class LibcommEnabler extends BaseLibraryEnabler implements
		LibraryEnabler {

	/* **************************** Constructors *************************** */

	public LibcommEnabler(String name, Enabler primaryEnabler,
			Evaluator evaluator, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer) {
		super(name, primaryEnabler, evaluator, modelFactory, symbolicUtil,
				symbolicAnalyzer);
	}

	/* ********************* Methods from LibraryEnabler ******************* */

	@Override
	public Set<Integer> ampleSet(State state, int pid,
			CallOrSpawnStatement statement,
			Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		CallOrSpawnStatement call;

		if (!(statement instanceof CallOrSpawnStatement)) {
			throw new CIVLInternalException("Unsupported statement for civlc",
					statement);
		}
		call = (CallOrSpawnStatement) statement;
		name = call.function().name();
		switch (name.name()) {
		case "$comm_enqueue":
		case "$comm_dequeue":
			return ampleSetWork(state, pid, call, reachableMemUnitsMap);
		default:
			return super.ampleSet(state, pid, statement, reachableMemUnitsMap);
		}
	}

	@Override
	public List<Transition> enabledTransitions(State state,
			CallOrSpawnStatement call, BooleanExpression pathCondition,
			int pid, int processIdentifier, Statement assignAtomicLock)
			throws UnsatisfiablePathConditionException {
		String functionName = call.function().name().name();

		switch (functionName) {
		case "$comm_dequeue":
			return this.enabledCommDequeueTransitions(state, call,
					pathCondition, pid, processIdentifier, assignAtomicLock);
		default:
			return super.enabledTransitions(state, call, pathCondition, pid,
					processIdentifier, assignAtomicLock);
		}
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Computes the ample set process ID's from a system function call.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the system function call belongs
	 *            to.
	 * @param call
	 *            The system function call statement.
	 * @param reachableMemUnitsMap
	 *            The map of reachable memory units of all active processes.
	 * @return
	 */
	private Set<Integer> ampleSetWork(State state, int pid,
			CallOrSpawnStatement call,
			Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap) {
		int numArgs;
		numArgs = call.arguments().size();
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		String function = call.function().name().name();
		CIVLSource source = call.getSource();
		Set<Integer> ampleSet = new HashSet<>();

		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = null;

			arguments[i] = call.arguments().get(i);
			try {
				eval = evaluator.evaluate(state, pid, arguments[i]);
			} catch (UnsatisfiablePathConditionException e) {
				return new HashSet<>();
			}
			argumentValues[i] = eval.value;
			state = eval.state;
		}

		switch (function) {
		case "$comm_dequeue":
			NumericExpression argSrc = (NumericExpression) argumentValues[1];
			Reasoner reasoner = universe.reasoner(state.getPathCondition());

			// TODO: fix me.
			// If it's a wild card source comm_dequeue, all processes in
			// the same communicator will be added into ample set.
			if (reasoner.isValid(universe.lessThanEquals(zero, argSrc))) {
				return this.computeAmpleSetByHandleObject(state, pid,
						arguments[0], argumentValues[0], reachableMemUnitsMap);
			} else {
				// TODO: find out processes in the gcomm, instead of all
				// processes of the system.
				for (int p : reachableMemUnitsMap.keySet()) {
					ampleSet.add(p);
				}
			}
			return ampleSet;
		case "$comm_enqueue":
			// Because we don't know if other processes will call an wild card
			// receive(dequeue), we have to put all processes into ample set.
			return this.computeAmpleSetByHandleObject(state, pid, arguments[0],
					argumentValues[0], reachableMemUnitsMap);
		default:
			throw new CIVLInternalException("Unreachable" + function, source);
		}
	}

	/**
	 * Emanating one or multiple transitions from the given state which is at
	 * the location: $comm_dequeue().
	 * 
	 * @param state
	 *            The current state.
	 * @param call
	 *            The function call statement, upon which the set of enabled
	 *            transitions will be computed.
	 * @param pathCondition
	 *            The current path condition.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param processIdentifier
	 *            The identifier of the process
	 * @param assignAtomicLock
	 *            The assignment statement for the atomic lock variable, should
	 *            be null except that the process is going to re-obtain the
	 *            atomic lock variable.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private List<Transition> enabledCommDequeueTransitions(State state,
			CallOrSpawnStatement call, BooleanExpression pathCondition,
			int pid, int processIdentifier, Statement assignAtomicLock)
			throws UnsatisfiablePathConditionException {
		List<Expression> arguments = call.arguments();
		List<Transition> localTransitions = new LinkedList<>();
		Evaluation eval;
		String process = "p" + processIdentifier + " (id = " + pid + ")";
		// Since both source and tag may be wild card, there are at most 4
		// situations that will cause different results.
		BooleanExpression isAnySource = null;
		BooleanExpression sourceGTEzero = null;
		BooleanExpression isAnyTag = null;
		BooleanExpression tagGTEzero = null;
		// The reasoner used to prove if clauses above are valid
		Reasoner reasoner = universe.reasoner(pathCondition);
		// Flag indicates if we need to add clauses to original path
		// condition.
		NumericExpression minusOne = universe.integer(-1);
		NumericExpression minusTwo = universe.integer(-2);
		IntegerNumber argSourceNumber, argTagNumber;
		NumericExpression argSource, argTag;
		List<SymbolicExpression> possibleSources;
		Expression commHandleExpr, sourceExpr, tagExpr;
		SymbolicExpression gcommHandle, gcomm, comm, commHandle, source, dest, tag;
		BooleanExpression T = universe.trueExpression();
		BooleanExpression newPathCondition = universe.and(T, pathCondition);
		// Set of transition statements
		List<Statement> callWorkers = new LinkedList<>();
		// Set of new clauses
		List<BooleanExpression> newClauses = new LinkedList<>();

		eval = this.evaluator.evaluate(state.setPathCondition(pathCondition),
				pid, arguments.get(1));
		argSourceNumber = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) eval.value);
		if (argSourceNumber == null)
			argSource = (NumericExpression) eval.value;
		else
			argSource = universe.integer(argSourceNumber.intValue());
		eval = this.evaluator.evaluate(eval.state, pid, arguments.get(2));
		argTagNumber = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) eval.value);
		if (argTagNumber == null)
			argTag = (NumericExpression) eval.value;
		else
			argTag = universe.integer(argTagNumber.intValue());
		// clause: source >= 0
		sourceGTEzero = universe.lessThanEquals(zero, argSource);
		if (!reasoner.isValid(sourceGTEzero)) {
			// clause: source == 0
			// TODO: can source be non-concrete
			isAnySource = universe.equals(minusOne, argSource);
			if (!reasoner.isValid(isAnySource)) {
				isAnyTag = universe.equals(minusTwo, argTag);
				if (!reasoner.isValid(isAnyTag)) {
					tagGTEzero = universe.lessThanEquals(zero, argTag);
					if (!reasoner.isValid(isAnyTag)) {
						newClauses.add(universe.and(isAnySource, isAnyTag));
						newClauses.add(universe.and(isAnySource, tagGTEzero));
						newClauses.add(universe.and(sourceGTEzero, isAnyTag));
						newClauses.add(universe.and(sourceGTEzero, tagGTEzero));
					}
				}
				if (newClauses.isEmpty()) {
					newClauses.add(isAnySource);
					newClauses.add(sourceGTEzero);
				}
			}
		}
		if (newClauses.isEmpty())
			newClauses.add(universe.trueExpression());
		// Initialize arguments
		possibleSources = new LinkedList<>();
		commHandleExpr = arguments.get(0);
		sourceExpr = arguments.get(1);
		tagExpr = arguments.get(2);
		commHandle = evaluator.evaluate(state, pid, commHandleExpr).value;
		comm = evaluator.dereference(commHandleExpr.getSource(), state,
				process, commHandle, false).value;
		source = argSource;
		dest = this.universe.tupleRead(comm, zeroObject);
		tag = argTag;
		gcommHandle = this.universe.tupleRead(comm, oneObject);
		gcomm = evaluator.dereference(commHandleExpr.getSource(), state,
				process, gcommHandle, false).value;
		for (int i = 0; i < newClauses.size(); i++) {
			BooleanExpression newClause = newClauses.get(i);

			// TODO: changing call.guard to T or null because it will never be
			// used in the future.
			newPathCondition = universe.and(pathCondition, newClause);
			possibleSources = getAllPossibleSources(eval.state, newClause,
					gcomm, source, dest, tag, call.getSource());
			callWorkers = (List<Statement>) this.dequeueStatementGenerator(
					sourceExpr, tagExpr, possibleSources, newPathCondition,
					call.getSource(), call.function().parameters(), arguments,
					call.function().returnType(), call.statementScope(),
					call.guard(), call.target(), call.lhs(), assignAtomicLock);
			for (int j = 0; j < callWorkers.size(); j++)
				localTransitions.add(Semantics.newTransition(newPathCondition,
						pid, processIdentifier, callWorkers.get(j)));
		}
		return localTransitions;
	}

	// TODO: doc
	private Iterable<Statement> dequeueStatementGenerator(
			Expression sourceExpr, Expression tagExpr,
			List<SymbolicExpression> possibleSources,
			BooleanExpression pathCondition, CIVLSource civlsource,
			List<Variable> parameters, List<Expression> arguments,
			CIVLType returnType, Scope containingScope, Expression callGuard,
			Location callTarget, LHSExpression lhs, Statement assignAtomicLock)
			throws UnsatisfiablePathConditionException {
		CallOrSpawnStatement callWorker;
		Statement transitionStatement;
		List<Statement> transitionStatements = new LinkedList<>();
		List<Expression> newArgs;
		SystemFunction dequeueWorkFunction;
		FunctionIdentifierExpression dequeueWorkPointer;
		Location newLocation = null;
		String dequeueWork = "$comm_dequeue_work";
		Iterator<SymbolicExpression> sourceIter;
		Reasoner reasoner = universe.reasoner(pathCondition);

		sourceIter = possibleSources.iterator();
		while (sourceIter.hasNext()) {
			SymbolicExpression newSource = sourceIter.next();
			int int_newSource = ((IntegerNumber) reasoner
					.extractNumber((NumericExpression) newSource)).intValue();

			// TODO: can these be a parameter ?
			dequeueWorkFunction = modelFactory.systemFunction(civlsource,
					modelFactory.identifier(civlsource, dequeueWork),
					parameters, returnType, containingScope, this.name);
			dequeueWorkPointer = modelFactory.functionPointerExpression(
					civlsource, dequeueWorkFunction);
			newArgs = new LinkedList<Expression>(arguments);
			newArgs.set(1, modelFactory.integerLiteralExpression(
					arguments.get(1).getSource(),
					BigInteger.valueOf(int_newSource)));
			newLocation = modelFactory.location(civlsource, containingScope);
			callWorker = modelFactory.callOrSpawnStatement(civlsource,
					newLocation, true, newArgs, callGuard);
			callWorker.setTargetTemp(callTarget);
			callWorker.setFunction(dequeueWorkPointer);
			callWorker.setLhs(lhs);
			if (assignAtomicLock != null) {
				transitionStatement = modelFactory.statmentList(
						assignAtomicLock, callWorker);
			} else {
				transitionStatement = callWorker;
			}
			transitionStatements.add(transitionStatement);
		}

		return transitionStatements;
	}

	/**
	 * <p>
	 * This function checks all message channels (messages receiving buffers) to
	 * seek for available sources. If there are at least one message specified
	 * by "tag" argument in the channel specified by the "source" argument(and
	 * other arguments of course, but here only "source" will make any
	 * difference), the "source" is available.
	 * </p>
	 * <p>
	 * Precondition: The "predicate" argument shall be able to determine weather
	 * the "source" or "tag" is wild card or valid specific symbolic expression.
	 * </p>
	 * 
	 * @author Ziqing Luo
	 * @param predicate
	 *            Context conditions which helps determining weather the source
	 *            or tag is a wild card. This argument shall be able to
	 *            certainly prove: if the "source" belongs to [0, infinity) or
	 *            {-1} and if the "tag" belongs to [0, infinity) or {-2}.
	 * @param gcomm
	 *            The global communicator
	 * @param source
	 *            The argument "source" which indicates some message
	 *            channels(message queue in our implementation).
	 * @param dest
	 *            The argument "dest" which indicates the receiving process
	 *            itself.
	 * @param tag
	 *            The argument "tag" which indicates some messages have the same
	 *            tag.
	 * @param civlsource
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private List<SymbolicExpression> getAllPossibleSources(State state,
			BooleanExpression predicate, SymbolicExpression gcomm,
			SymbolicExpression source, SymbolicExpression dest,
			SymbolicExpression tag, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression buf;
		SymbolicExpression bufRow;
		SymbolicExpression queue;
		SymbolicExpression queueLength;
		SymbolicExpression messages = null;
		SymbolicExpression message = null;
		BooleanExpression newPathConditions = universe.and(predicate,
				state.getPathCondition());
		Reasoner reasoner = universe.reasoner(newPathConditions);
		IntegerNumber sourceNumber = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) source);
		IntegerNumber tagNumber = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) tag);
		List<SymbolicExpression> results = new LinkedList<>();
		boolean isWildcardSource = false, isWildcardTag = false;

		if (newPathConditions.equals(universe.falseExpression()))
			return results;

		if (sourceNumber != null && sourceNumber.intValue() == -1)
			isWildcardSource = true;
		if (tagNumber != null && tagNumber.intValue() == -2)
			isWildcardTag = true;

		buf = universe.tupleRead(gcomm, universe.intObject(2));
		// non-wild card source and tag
		if (!isWildcardSource && !isWildcardTag) {
			BooleanExpression iterLTQueueLengthClaim;
			NumericExpression iter = universe.integer(0);

			bufRow = universe.arrayRead(buf, (NumericExpression) source);
			queue = universe.arrayRead(bufRow, (NumericExpression) dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = universe.tupleRead(queue, zeroObject);
			iterLTQueueLengthClaim = universe.lessThan(iter,
					(NumericExpression) queueLength);
			while (reasoner.isValid(iterLTQueueLengthClaim)) {
				BooleanExpression tagMatchClaim;

				message = universe.arrayRead(messages, iter);
				tagMatchClaim = universe.equals(
						universe.tupleRead(message, twoObject), tag);
				if (reasoner.isValid(tagMatchClaim)) {
					results.add(source);
					break;
				}
				iter = universe.add(iter, one);
				iterLTQueueLengthClaim = universe.lessThan(iter,
						(NumericExpression) queueLength);
			}
		}// non-wild card source and any_tag
		else if (!isWildcardSource && isWildcardTag) {
			bufRow = universe.arrayRead(buf, (NumericExpression) source);
			queue = universe.arrayRead(bufRow, (NumericExpression) dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = universe.tupleRead(queue, zeroObject);
			if (reasoner.isValid(universe.lessThan(zero,
					(NumericExpression) queueLength)))
				results.add(source);
		} // any source and non-wild card tag
		else if (isWildcardSource && !isWildcardTag) {
			NumericExpression nprocs = (NumericExpression) universe.tupleRead(
					gcomm, zeroObject);
			NumericExpression iter = universe.zeroInt();
			BooleanExpression iterLTnprocsClaim = universe.lessThan(iter,
					nprocs);

			while (reasoner.isValid(iterLTnprocsClaim)) {
				NumericExpression queueIter = universe.zeroInt();
				BooleanExpression queueIterLTlengthClaim;

				bufRow = universe.arrayRead(buf, iter);
				queue = universe.arrayRead(bufRow, (NumericExpression) dest);
				messages = universe.tupleRead(queue, oneObject);
				queueLength = universe.tupleRead(queue, zeroObject);
				queueIterLTlengthClaim = universe.lessThan(queueIter,
						(NumericExpression) queueLength);
				while (reasoner.isValid(queueIterLTlengthClaim)) {
					BooleanExpression tagMatchClaim;

					message = universe.arrayRead(messages, queueIter);
					tagMatchClaim = universe.equals(
							universe.tupleRead(message, twoObject), tag);
					if (reasoner.isValid(tagMatchClaim)) {
						results.add(iter);
						break;
					}
					queueIter = universe.add(queueIter, one);
					queueIterLTlengthClaim = universe.lessThan(queueIter,
							(NumericExpression) queueLength);
				}
				iter = universe.add(iter, one);
				iterLTnprocsClaim = universe.lessThan(iter, nprocs);
			}
		} else if (isWildcardSource && isWildcardTag) {
			NumericExpression nprocs = (NumericExpression) universe.tupleRead(
					gcomm, zeroObject);
			NumericExpression iter = universe.zeroInt();
			BooleanExpression iterLTnprocsClaim = universe.lessThan(iter,
					nprocs);

			while (reasoner.isValid(iterLTnprocsClaim)) {
				bufRow = universe.arrayRead(buf, iter);
				queue = universe.arrayRead(bufRow, (NumericExpression) dest);
				messages = universe.tupleRead(queue, oneObject);
				queueLength = universe.tupleRead(queue, zeroObject);
				if (reasoner.isValid(universe.lessThan(zero,
						(NumericExpression) queueLength))) {
					results.add(iter);
				}
				iter = universe.add(iter, one);
				iterLTnprocsClaim = universe.lessThan(iter, nprocs);
			}
		}
		return results;
	}
}
