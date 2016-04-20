package edu.udel.cis.vsl.civl.library.comm;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
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
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
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
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			LibraryEnablerLoader libEnablerLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryEnabler, evaluator, modelFactory, symbolicUtil,
				symbolicAnalyzer, libEnablerLoader, libEvaluatorLoader);
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
		Reasoner reasoner = universe.reasoner(pathCondition);
		IntegerNumber argSourceNumber; // numeric object of the value of source
		IntegerNumber argTagNumber; // numeric object of the value of tag
		int intSource;
		int intTag;
		// set of all available sources
		List<NumericExpression> possibleSources;
		Expression commHandleExpr, sourceExpr, tagExpr;
		SymbolicExpression gcommHandle, gcomm, comm, commHandle, dest;
		// Set of transition statements
		List<Statement> callWorkers = new LinkedList<>();
		boolean isWildcardSrc = false;

		// evaluate the second argument: source
		eval = this.evaluator.evaluate(state.setPathCondition(pathCondition),
				pid, arguments.get(1));
		state = eval.state;
		argSourceNumber = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) eval.value);
		if (argSourceNumber == null)
			throw new CIVLUnimplementedFeatureException(
					"CIVL doesn't support using non-concrete source of messages \n",
					arguments.get(1).getSource());
		else
			intSource = argSourceNumber.intValue();
		// evaluate the third argument: tag
		eval = this.evaluator.evaluate(eval.state, pid, arguments.get(2));
		argTagNumber = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) eval.value);
		if (argTagNumber == null)
			throw new CIVLUnimplementedFeatureException(
					"CIVL doesn't support using non-concrete message tag\n",
					arguments.get(2).getSource());
		else
			intTag = argTagNumber.intValue();

		// clause: source >= 0
		// If and only if "source < 0" is true, the "comm_dequeue()" becomes
		// non-deterministic.
		if (intSource == -1)
			isWildcardSrc = true;
		// Initialize arguments
		possibleSources = new LinkedList<>();
		commHandleExpr = arguments.get(0);
		sourceExpr = arguments.get(1);
		tagExpr = arguments.get(2);
		commHandle = evaluator.evaluate(state, pid, commHandleExpr).value;
		comm = evaluator.dereference(commHandleExpr.getSource(), state,
				process, commHandle, false).value;
		dest = this.universe.tupleRead(comm, zeroObject);
		gcommHandle = this.universe.tupleRead(comm, oneObject);
		gcomm = evaluator.dereference(commHandleExpr.getSource(), state,
				process, gcommHandle, false).value;
		assert (dest instanceof NumericExpression) : "Argument of destination of $comm_dequeue() should be a numeric type.\n";
		if (isWildcardSrc) {
			LibcommEvaluator libevaluator;

			try {
				libevaluator = (LibcommEvaluator) this.libEvaluatorLoader
						.getLibraryEvaluator(this.name, evaluator,
								this.modelFactory, symbolicUtil,
								symbolicAnalyzer);
				possibleSources = libevaluator.getAllPossibleSources(
						eval.state, reasoner, gcomm, intSource, intTag,
						(NumericExpression) dest, call.getSource());
			} catch (LibraryLoaderException e) {
				throw new CIVLInternalException(
						"LibraryLoader exception happens when loading library comm evaluator.\n",
						call.getSource());
			}
			possibleSources = libevaluator.getAllPossibleSources(eval.state,
					reasoner, gcomm, intSource, intTag,
					(NumericExpression) dest, call.getSource());
			callWorkers = (List<Statement>) this.dequeueStatementGenerator(
					sourceExpr, tagExpr, possibleSources, call.getSource(),
					call.function().parameters(), arguments, call.function()
							.returnType(), call.statementScope(), call.guard(),
					call.target(), call.lhs(), assignAtomicLock);
			for (int j = 0; j < callWorkers.size(); j++)
				localTransitions.add(Semantics.newTransition(pathCondition,
						pid, processIdentifier, callWorkers.get(j)));
		} else
			localTransitions.add(Semantics.newTransition(pathCondition, pid,
					processIdentifier, call));
		return localTransitions;
	}

	/**
	 * Generates a list of "comm_dequeue()" statements whose second argument
	 * "source" is always non-wild card and has a exact concrete value, which is
	 * decided by the passed in list of numbers of all possible sources. This
	 * method also helps building the statement expression from a bunch of
	 * parameters and configurations.
	 * 
	 * @param sourceExpr
	 *            The expression of source argument of the function statement
	 * @param tagExpr
	 *            The expression of tag argument of the function statement
	 * @param possibleSources
	 *            The list contains all possible values of the source argument.
	 * @param civlsource
	 *            CIVL source of the function statement
	 * @param parameters
	 *            A list of {@link Variable}s of parameters of the function
	 * @param arguments
	 *            A list of {@link Expression}s of parameters of the function
	 * @param returnType
	 *            The CIVL type of the function return type
	 * @param containingScope
	 *            The containing scope of the function in this statement.
	 * @param callGuard
	 *            The guard of this statement
	 * @param callTarget
	 *            The target location of the function statement
	 * @param lhs
	 *            The left hand side expression of this function statement
	 * @param assignAtomicLock
	 *            The assignment statement for the atomic lock variable, should
	 *            be null except that the process is going to re-obtain the
	 *            atomic lock variable.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Iterable<Statement> dequeueStatementGenerator(
			Expression sourceExpr, Expression tagExpr,
			List<NumericExpression> possibleSources, CIVLSource civlsource,
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

		for (NumericExpression newSource : possibleSources) {
			int int_newSource;

			try {
				int_newSource = ((IntegerNumber) universe
						.extractNumber(newSource)).intValue();
			} catch (ClassCastException e) {
				throw new CIVLInternalException(
						"Unexpected exception when casting Number object of a value of a message source to IntegerNumber object.\n",
						civlsource);
			}
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
}
