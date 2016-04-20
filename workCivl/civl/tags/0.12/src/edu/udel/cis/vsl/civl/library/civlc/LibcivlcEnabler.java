package edu.udel.cis.vsl.civl.library.civlc;

import java.io.PrintStream;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.library.IF.BaseLibraryEnabler;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionPointerExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

/**
 * Implementation of the enabler-related logics for system functions declared
 * civlc.h.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibcivlcEnabler extends BaseLibraryEnabler implements
		LibraryEnabler {

	private static String chooseIntWork = "$choose_int_work";
	private FunctionPointerExpression chooseIntWorkPointer;
	private LibcivlcEvaluator libEvaluator;

	/* **************************** Constructors *************************** */
	/**
	 * Creates a new instance of the library enabler for civlc.h.
	 * 
	 * @param primaryEnabler
	 *            The enabler for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param modelFactory
	 *            The model factory of the system.
	 */
	public LibcivlcEnabler(String name, Enabler primaryEnabler,
			Evaluator evaluator, PrintStream output, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil) {
		super(name, primaryEnabler, evaluator, output, modelFactory,
				symbolicUtil);
		CIVLSource source = modelFactory.model().getSource();
		SystemFunction chooseIntWorkFunction = modelFactory.systemFunction(
				source,
				modelFactory.identifier(source, chooseIntWork),
				Arrays.asList(modelFactory.variable(source,
						modelFactory.integerType(),
						modelFactory.identifier(source, "n"), 0)),
				modelFactory.integerType(), modelFactory.model().system()
						.containingScope(), "civlc");

		chooseIntWorkPointer = modelFactory.functionPointerExpression(source,
				chooseIntWorkFunction);
		this.libEvaluator = new LibcivlcEvaluator(name, evaluator,
				modelFactory, symbolicUtil);

	}

	/* ********************* Methods from LibraryEnabler ******************* */

	@Override
	public Set<Integer> ampleSet(State state, int pid,
			CallOrSpawnStatement statement,
			Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap) {
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
		CallOrSpawnStatement callWorker;
		List<Expression> arguments = call.arguments();
		List<Transition> localTransitions = new LinkedList<>();
		Statement transitionStatement;
		Evaluation eval;
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		switch (functionName) {
		case "$choose_int":
			eval = evaluator.evaluate(state.setPathCondition(pathCondition),
					pid, arguments.get(0));
			IntegerNumber upperNumber = (IntegerNumber) universe.reasoner(
					eval.state.getPathCondition()).extractNumber(
					(NumericExpression) eval.value);
			int upper;

			if (upperNumber == null) {
				throw new CIVLExecutionException(ErrorKind.INTERNAL,
						Certainty.NONE, process,
						"Argument to $choose_int not concrete: " + eval.value,
						symbolicUtil.stateToString(state), arguments.get(0)
								.getSource());
			}
			upper = upperNumber.intValue();
			for (int i = 0; i < upper; i++) {
				Expression workerArg = modelFactory.integerLiteralExpression(
						arguments.get(0).getSource(), BigInteger.valueOf(i));

				callWorker = modelFactory.callOrSpawnStatement(
						call.getSource(), null, true, Arrays.asList(workerArg),
						null);
				callWorker.setTargetTemp(call.target());
				callWorker.setFunction(chooseIntWorkPointer);
				callWorker.setLhs(call.lhs());
				if (assignAtomicLock != null) {
					transitionStatement = modelFactory.statmentList(
							assignAtomicLock, callWorker);
				} else {
					transitionStatement = callWorker;
				}
				localTransitions.add(Semantics.newTransition(pathCondition,
						pid, processIdentifier, transitionStatement));
			}
			break;
		case "$comm_dequeue":
			localTransitions.addAll(this.enabledCommDequeueTransitions(state,
					call, pathCondition, pid, processIdentifier,
					assignAtomicLock));
			break;
		default:
			return super.enabledTransitions(state, call, pathCondition, pid,
					processIdentifier, assignAtomicLock);
		}
		return localTransitions;
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

			if (reasoner.isValid(universe.lessThanEquals(zero, argSrc))) {
				ampleSet.addAll(this.computeAmpleSetByHandleObject(state, pid,
						arguments[0], argumentValues[0], reachableMemUnitsMap));
			} else {
				for (int p : reachableMemUnitsMap.keySet()) {
					ampleSet.add(p);
				}
			}
			return ampleSet;
		case "$comm_enqueue":
			ampleSet.addAll(this.computeAmpleSetByHandleObject(state, pid,
					arguments[0], argumentValues[0], reachableMemUnitsMap));
			return ampleSet;
		default:
			throw new CIVLInternalException("Unreachable" + function, source);
		}
	}

	/**
	 * Computes the ample set by analyzing the given handle object for the
	 * statement.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The pid of the process
	 * @param handleObj
	 *            The expression of the given handle object
	 * @param handleObjValue
	 *            The symbolic expression of the given handle object
	 * @param reachableMemUnitsMap
	 *            The map contains all reachable memory units of all processes
	 * @return
	 */
	private Set<Integer> computeAmpleSetByHandleObject(State state, int pid,
			Expression handleObj, SymbolicExpression handleObjValue,
			Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap) {
		Set<SymbolicExpression> handleObjMemUnits = new HashSet<>();
		Set<Integer> ampleSet = new HashSet<Integer>();

		try {
			evaluator.memoryUnitsOfExpression(state, pid, handleObj,
					handleObjMemUnits);
		} catch (UnsatisfiablePathConditionException e) {
			handleObjMemUnits.add(handleObjValue);
		}
		for (SymbolicExpression memUnit : handleObjMemUnits) {
			for (int otherPid : reachableMemUnitsMap.keySet()) {
				if (otherPid == pid || ampleSet.contains(otherPid))
					continue;
				else if (reachableMemUnitsMap.get(otherPid)
						.containsKey(memUnit)) {
					ampleSet.add(otherPid);
				}
			}
		}
		return ampleSet;
	}

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
		FunctionPointerExpression dequeueWorkPointer;
		Location newLocation = null;
		String dequeueWork = "$comm_dequeue_work";
		Iterator<SymbolicExpression> sourceIter;

		Reasoner reasoner = universe.reasoner(pathCondition);

		sourceIter = possibleSources.iterator();
		while (sourceIter.hasNext()) {
			SymbolicExpression newSource = sourceIter.next();
			int int_newSource = ((IntegerNumber) reasoner
					.extractNumber((NumericExpression) newSource)).intValue();

			dequeueWorkFunction = modelFactory.systemFunction(civlsource,
					modelFactory.identifier(civlsource, dequeueWork),
					parameters, returnType, containingScope, "civlc");
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

	/* ********* Private Separate transitions enabling functions *********** */
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

			newPathCondition = universe.and(pathCondition, newClause);
			possibleSources = libEvaluator.getAllPossibleSources(eval.state,
					newClause, gcomm, source, dest, tag, call.getSource());
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

	// private List<Transition> enableBundleUnpackApplyTransitions(State state,
	// CallOrSpawnStatement call, BooleanExpression pathCondition,
	// int pid, int processIdentifier, Statement assignAtomicLock)
	// throws UnsatisfiablePathConditionException {
	// List<Expression> arguments = call.arguments();
	// List<Transition> localTransitions = new LinkedList<>();
	// Evaluation eval;
	// String process = "p" + processIdentifier + " (id = " + pid + ")";
	// // For now, only CIVL_MAX and CIVL_MIN operation need to enable multiple
	// // transitions.
	// Reasoner reasoner = universe.reasoner(pathCondition);
	// Expression civlOpExpr = arguments.get(3);
	// Expression bundleExpr = arguments.get(0);
	// Expression otherDataPtrExpr = arguments.get(1);
	// Expression countExpr = arguments.get(2);
	// NumericExpression civlOp;
	// NumericExpression count;
	// NumericExpression i = zero;
	// SymbolicExpression otherDataPtr = null;
	// SymbolicExpression data = null, otherData = null;
	// List<SymbolicExpression> dataList, otherDataList;
	// BooleanExpression claim;
	// ReferenceExpression ref;
	// List<BooleanExpression> predicates = new LinkedList<>();
	// IntegerNumber civlOpNumber;
	// CIVLOperation op;
	//
	// eval = evaluator.evaluate(state, pid, civlOpExpr);
	// civlOp = (NumericExpression) eval.value;
	// civlOpNumber = (IntegerNumber) reasoner.extractNumber(civlOp);
	// if (civlOpNumber == null)
	// throw new CIVLUnimplementedFeatureException(
	// "non-concretet $operation", civlOpExpr.getSource());
	// op = CIVLOperation.values()[civlOpNumber.intValue()];
	// // If op is not max or min, return the original single transition
	// if (op != CIVLOperation.CIVL_MAX && op != CIVLOperation.CIVL_MIN)
	// super.enabledTransitions(state, call, pathCondition, pid,
	// processIdentifier, assignAtomicLock);
	// // else
	// data = symbolicUtil.bundleUnpack(
	// evaluator.evaluate(state, pid, bundleExpr).value, null, zero,
	// pathCondition);
	// otherDataPtr = evaluator.evaluate(state, pid, otherDataPtrExpr).value;
	// ref = symbolicUtil.getSymRef(otherDataPtr);
	// if (ref.isArrayElementReference()) {
	// int otherDataIndex;
	//
	// otherDataIndex = symbolicUtil.getArrayIndex(
	// otherDataPtrExpr.getSource(), otherDataPtr);
	// otherDataPtr = symbolicUtil.parentPointer(
	// otherDataPtrExpr.getSource(), otherDataPtr);
	// otherData = evaluator.dereference(otherDataPtrExpr.getSource(),
	// state, process, otherDataPtr, false).value;
	// otherData = symbolicUtil.getSubArray(otherData,
	// universe.integer(otherDataIndex),
	// universe.length(otherData), state, process,
	// otherDataPtrExpr.getSource());
	// } else {
	// otherData = evaluator.dereference(otherDataPtrExpr.getSource(),
	// state, process, otherDataPtr, false).value;
	// }
	// // ------unrolling data and otherData
	// dataList = symbolicUtil.arrayUnrolling(data, pathCondition);
	// otherDataList = symbolicUtil.arrayUnrolling(otherData, pathCondition);
	// if (dataList.size() > 0)
	// data = universe.array(dataList.get(0).type(), dataList);
	// else
	// data = null;
	// if (otherDataList.size() > 0)
	// otherData = universe.array(otherDataList.get(0).type(),
	// otherDataList);
	// else
	// otherData = null;
	// count = (NumericExpression) evaluator.evaluate(state, pid,
	// countExpr).value;
	// // ------checking elements in data and otherData one by one if they can
	// // be compared by the current path condition.
	// claim = universe.lessThan(i, count);
	// while (reasoner.isValid(claim)) {
	// NumericExpression dataEle, otherDataEle;
	//
	// dataEle = (NumericExpression) universe.arrayRead(data, i);
	// otherDataEle = (NumericExpression) universe.arrayRead(otherData, i);
	// claim = universe.lessThan(dataEle, otherDataEle);
	// if (!reasoner.isValid(claim)) {
	// claim = universe.lessThanEquals(otherDataEle, dataEle);
	// if (!reasoner.isValid(claim))
	// predicates.add(claim);
	// }
	//
	// }
	// return null;
	// }
}
