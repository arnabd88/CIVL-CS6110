package edu.udel.cis.vsl.civl.library.civlc;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.IF.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

public class LibcivlcEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	private IntObject twoObject = universe.intObject(2);
	private NumericExpression minusOne = universe.integer(-1);
	private NumericExpression minusTwo = universe.integer(-2);

	// Package private enumerator.
	// The order of these operations should be consistent with the civl-common.h
	// file.
	enum CIVLOperation {
		CIVL_NO_OP, // no operation
		CIVL_MAX, // maxinum
		CIVL_MIN, // minimun
		CIVL_SUM, // sum
		CIVL_PROD, // product
		CIVL_LAND, // logical and
		CIVL_BAND, // bit-wise and
		CIVL_LOR, // logical or
		CIVL_BOR, // bit-wise or
		CIVL_LXOR, // logical exclusive or
		CIVL_BXOR, // bit-wise exclusive or
		CIVL_MINLOC, // min value and location
		CIVL_MAXLOC, // max value and location
		CIVL_REPLACE // replace ? TODO: Find definition for this operation
	}

	public LibcivlcEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil) {
		super(name, evaluator, modelFactory, symbolicUtil);
	}

	@Override
	public Evaluation evaluateGuard(CIVLSource source, State state, int pid,
			String function, List<Expression> arguments)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression[] argumentValues;
		int numArgs;
		BooleanExpression guard;
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		numArgs = arguments.size();
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = null;

			try {
				eval = evaluator.evaluate(state, pid, arguments.get(i));
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return new Evaluation(state, universe.falseExpression());
			}
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (function) {
		case "$comm_dequeue":
			try {
				guard = getDequeueGuard(state, pid, process, arguments,
						argumentValues);
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return new Evaluation(state, universe.falseExpression());
			}
			break;
		case "$wait":
			guard = getWaitGuard(state, pid, arguments, argumentValues);
			break;
		case "$waitall":
			guard = getWaitAllGuard(state, pid, arguments, argumentValues);
			break;
		case "$barrier_exit":
			try {
				guard = getBarrierExitGuard(state, pid, process, arguments,
						argumentValues);
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return new Evaluation(state, universe.falseExpression());
			}
			break;
		default:
			guard = universe.trueExpression();
		}
		return new Evaluation(state, guard);
	}

	/**
	 * void $waitall($proc *procs, int numProcs);
	 * 
	 * @param state
	 * @param pid
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression getWaitAllGuard(State state, int pid,
			List<Expression> arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression procsPointer = argumentValues[0];
		SymbolicExpression numOfProcs = argumentValues[1];
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_nprocs = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) numOfProcs);
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		if (number_nprocs == null) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.OTHER, Certainty.PROVEABLE, process,
					"The number of processes for $waitall "
							+ "needs a concrete value.",
					symbolicUtil.stateToString(state), arguments.get(1)
							.getSource());

			this.errorLogger.reportError(err);
			return this.falseValue;
		} else {
			int numOfProcs_int = number_nprocs.intValue();
			BinaryExpression pointerAdd;
			CIVLSource procsSource = arguments.get(0).getSource();
			Evaluation eval;

			for (int i = 0; i < numOfProcs_int; i++) {
				Expression offSet = modelFactory.integerLiteralExpression(
						procsSource, BigInteger.valueOf(i));
				NumericExpression offSetV = universe.integer(i);
				SymbolicExpression procPointer, proc;
				int pidValue;

				pointerAdd = modelFactory.binaryExpression(procsSource,
						BINARY_OPERATOR.POINTER_ADD, arguments.get(0), offSet);
				eval = evaluator.pointerAdd(state, pid, process, pointerAdd,
						procsPointer, offSetV);
				procPointer = eval.value;
				state = eval.state;
				eval = evaluator.dereference(procsSource, state, process,
						procPointer, false);
				proc = eval.value;
				state = eval.state;
				pidValue = modelFactory.getProcessId(procsSource, proc);
				if (!state.getProcessState(pidValue).hasEmptyStack())
					return this.falseValue;
			}
		}
		return this.trueValue;
	}

	/**
	 * Computes the guard of $barrier_exit($barrier), i.e., when the
	 * corresponding cell of in_barrier array in $gbarrier is false.
	 * 
	 * @param state
	 * @param pid
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression getBarrierExitGuard(State state, int pid,
			String process, List<Expression> arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = arguments.get(0).getSource();
		SymbolicExpression barrier = argumentValues[0];
		NumericExpression myPlace;
		SymbolicExpression barrierObj;
		SymbolicExpression gbarrier;
		SymbolicExpression gbarrierObj;
		Evaluation eval = evaluator.dereference(source, state, process,
				barrier, false);
		SymbolicExpression inBarrierArray;
		SymbolicExpression meInBarrier;

		state = eval.state;
		barrierObj = eval.value;
		myPlace = (NumericExpression) universe
				.tupleRead(barrierObj, zeroObject);
		gbarrier = universe.tupleRead(barrierObj, oneObject);
		eval = evaluator.dereference(source, state, process, gbarrier, false);
		state = eval.state;
		gbarrierObj = eval.value;
		inBarrierArray = universe.tupleRead(gbarrierObj, twoObject);
		meInBarrier = universe.arrayRead(inBarrierArray, myPlace);
		if (meInBarrier.isTrue())
			return universe.falseExpression();
		return universe.trueExpression();
	}

	/**
	 * <p>
	 * Generate the a predicate stands for the guard of $comm_dequeue(). To
	 * evaluate if there is any message available, we add 4 predicates which
	 * will cover all valid situations together and each individual predicate
	 * may cause different results. The 4 predicates are: <br>
	 * 1. (source == -1 && tag == -2) <br>
	 * 2. (source >= 0 && tag == -2) <br>
	 * 3. (source == -1 && tag >= 0 ) <br>
	 * 4. (source >= 0 && tag >= 0 )
	 * 
	 * The returned predicate will be in a form as: (predicate1 &&
	 * (evaluate(predicate1)) ||...|| predicate4 && (evaluate(predicate4)))
	 * </p>
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param pid
	 *            The process id
	 * @param arguments
	 *            Expressions of arguments of the "$comm_dequeue()"function:
	 *            $comm, source, tag.
	 * @param argumentValues
	 *            Symbolic Expressions of arguments of the
	 *            "$comm_dequeue()"function.
	 * @return A predicate which is the guard of the function $comm_dequeue().
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression getDequeueGuard(State state, int pid,
			String process, List<Expression> arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression source = argumentValues[1];
		SymbolicExpression tag = argumentValues[2];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		SymbolicExpression dest;
		BooleanExpression sourceGTEzero, isAnySource, isAnyTag, tagGTEzero;
		BooleanExpression guard;
		List<BooleanExpression> predicates = new LinkedList<>();
		CIVLSource civlsource = arguments.get(0).getSource();
		Evaluation eval;

		eval = evaluator.dereference(civlsource, state, process, commHandle,
				false);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gcommHandle,
				false);
		state = eval.state;
		gcomm = eval.value;
		dest = universe.tupleRead(comm, zeroObject);
		sourceGTEzero = universe.lessThanEquals(zero,
				(NumericExpression) source);
		tagGTEzero = universe.lessThanEquals(zero, (NumericExpression) tag);
		isAnySource = universe.equals(source, minusOne);
		isAnyTag = universe.equals(tag, minusTwo);
		predicates = new LinkedList<>();
		predicates.add(universe.and(isAnySource, isAnyTag));
		predicates.add(universe.and(isAnySource, tagGTEzero));
		predicates.add(universe.and(sourceGTEzero, isAnyTag));
		predicates.add(universe.and(sourceGTEzero, tagGTEzero));
		guard = dequeueGuardGenerator(civlsource, state, predicates, gcomm,
				source, dest, tag);
		return guard;
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
	List<SymbolicExpression> getAllPossibleSources(State state,
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

	/**
	 * Computes the guard of $wait.
	 * 
	 * @param state
	 * @param pid
	 * @param arguments
	 * @param argumentValues
	 * @return
	 */
	private BooleanExpression getWaitGuard(State state, int pid,
			List<Expression> arguments, SymbolicExpression[] argumentValues) {
		SymbolicExpression joinProcess = argumentValues[0];
		BooleanExpression guard;
		int pidValue;
		Expression joinProcessExpr = arguments.get(0);

		if (joinProcess.operator() != SymbolicOperator.CONCRETE) {
			String process = state.getProcessState(pid).name() + "(id=" + pid
					+ ")";
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.OTHER, Certainty.PROVEABLE, process,
					"The argument of $wait should be concrete, but the actual value is "
							+ joinProcess + ".",
					symbolicUtil.stateToString(state),
					joinProcessExpr.getSource());

			this.errorLogger.reportError(err);
		}
		pidValue = modelFactory.getProcessId(joinProcessExpr.getSource(),
				joinProcess);
		if (modelFactory.isPocessIdDefined(pidValue)
				&& !modelFactory.isProcessIdNull(pidValue)
				&& !state.getProcessState(pidValue).hasEmptyStack())
			guard = universe.falseExpression();
		else
			guard = universe.trueExpression();
		return guard;
	}

	/**
	 * <p>
	 * Combining the given predicates and the results of evaluation on those
	 * predicates for the <code>$comm_dequeue()</code>.
	 * </p>
	 * 
	 * @author Ziqing Luo
	 * @param civlsource
	 *            The CIVL program source of the statement.
	 * @param state
	 *            Current state
	 * @param predicates
	 *            The set of predicates
	 * @param gcomm
	 *            The global communicator
	 * @param source
	 *            The source from where "$comm_dequeue" receives messages.
	 * @param dest
	 *            The destination which is the receiver itself
	 * @param tag
	 *            The message tag
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression dequeueGuardGenerator(CIVLSource civlsource,
			State state, Iterable<BooleanExpression> predicates,
			SymbolicExpression gcomm, SymbolicExpression source,
			SymbolicExpression dest, SymbolicExpression tag)
			throws UnsatisfiablePathConditionException {
		Iterator<BooleanExpression> predIter = predicates.iterator();
		BooleanExpression predicate;
		BooleanExpression guardComponent;
		BooleanExpression guard = universe.falseExpression();
		BooleanExpression hasMsg;

		do {
			predicate = predIter.next();
			hasMsg = universe.bool(!getAllPossibleSources(state, predicate,
					gcomm, source, dest, tag, civlsource).isEmpty());
			guardComponent = universe.and(predicate, hasMsg);
			guard = universe.or(guard, guardComponent);
		} while (predIter.hasNext());

		return guard;
	}

	/**
	 * Completing an operation (which is included in CIVLOperation enumerator).
	 * 
	 * @author Ziqing Luo
	 * @param arg0
	 *            The new data got from the bundle
	 * @param arg1
	 *            The data has already been received previously
	 * @param op
	 *            The CIVL Operation
	 * @return
	 */
	SymbolicExpression civlOperation(State state, String process,
			SymbolicExpression arg0, SymbolicExpression arg1, CIVLOperation op,
			CIVLSource civlsource) {
		BooleanExpression claim;

		/*
		 * For MAX and MIN operation, if CIVL cannot figure out a concrete
		 * result, make a abstract function for it.
		 */
		try {
			switch (op) {
			// TODO: consider using heuristic to switch to abstract
			// functions if these expressions get too big (max,min):
			case CIVL_MAX:
				claim = universe.lessThan((NumericExpression) arg1,
						(NumericExpression) arg0);
				return universe.cond(claim, arg0, arg1);
			case CIVL_MIN:
				claim = universe.lessThan((NumericExpression) arg0,
						(NumericExpression) arg1);
				return universe.cond(claim, arg0, arg1);
			case CIVL_SUM:
				return universe.add((NumericExpression) arg0,
						(NumericExpression) arg1);
			case CIVL_PROD:
				return universe.multiply((NumericExpression) arg0,
						(NumericExpression) arg1);
			case CIVL_LAND:
				return universe.and((BooleanExpression) arg0,
						(BooleanExpression) arg1);
			case CIVL_LOR:
				return universe.or((BooleanExpression) arg0,
						(BooleanExpression) arg1);
			case CIVL_LXOR:
				BooleanExpression notNewData = universe
						.not((BooleanExpression) arg0);
				BooleanExpression notPrevData = universe
						.not((BooleanExpression) arg1);

				return universe.or(
						universe.and(notNewData, (BooleanExpression) arg1),
						universe.and((BooleanExpression) arg0, notPrevData));
			case CIVL_BAND:
			case CIVL_BOR:
			case CIVL_BXOR:
			case CIVL_MINLOC:
			case CIVL_MAXLOC:
			case CIVL_REPLACE:
			default:
				throw new CIVLUnimplementedFeatureException("CIVLOperation: "
						+ op.name());
			}
		} catch (ClassCastException e) {
			throw new CIVLExecutionException(ErrorKind.OTHER,
					Certainty.PROVEABLE, process,
					"Invalid operands type for CIVL Operation: " + op.name(),
					civlsource);
		}
	}

	/* ************** Bundle unpacking and array operations **************** */
	/**
	 * Unpacking the given bundle, assigning the data in bundle to the object
	 * pointed by the given pointer.
	 * 
	 * Pre-Condition : Data in bundle is in the form of a unrolled one
	 * dimensional array.
	 * 
	 * Implementation details: First, it's guaranteed that the data in bundle is
	 * always in the form of a one dimensional array(also can be understood as a
	 * unrolled array or a sequence of data).<br>
	 * Second, inside this function, it contains a cast from the one dimensional
	 * array mentioned above to another type specified by the parameter
	 * "pointer". A correct CIVL program or C program should make sure that cast
	 * is legal, otherwise an error will be reported.<br>
	 * Third, the object used to store the data in bundle can have a larger size
	 * than the data itself.
	 * 
	 * @link 
	 *       {edu.udel.cis.vsl.civl.dynamic.common.CommonSymbolicUtility.arrayCasting
	 *       }
	 * @link {edu.udel.cis.vsl.civl.dynamic.common.CommonSymbolicUtility.
	 *       arrayUnrolling}
	 * 
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param bundle
	 *            The bundle type object
	 * @param pointer
	 *            The pointer to the address of the object which will be
	 *            assigned by bundle data
	 * @param civlsource
	 *            The CIVL Source of the bundle_unpack statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation bundleUnpack(State state, String process,
			SymbolicExpression bundle, SymbolicExpression pointer,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		if (!(bundle.type() instanceof SymbolicUnionType))
			throw new CIVLInternalException(
					"Bundle doesn't have a SymbolicUnionType", civlsource);
		SymbolicExpression data = (SymbolicExpression) bundle.argument(1);
		SymbolicExpression obj;
		SymbolicExpression array;
		NumericExpression dataSize;
		BooleanExpression claim;
		ReferenceExpression ref = symbolicUtil.getSymRef(pointer);
		SymbolicExpression unrolledDataArray = symbolicUtil.arrayUnrolling(
				state, process, data, civlsource);
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		Evaluation eval = new Evaluation(state, null);

		dataSize = universe.length(unrolledDataArray);
		// ------If data size is zero, do nothing
		if (reasoner.isValid(universe.equals(dataSize, zero)))
			return eval;

		// ------If pointer is an array element reference, the array is pointed
		// by the parent pointer.
		if (ref.isArrayElementReference()) {
			SymbolicExpression parentPtr = symbolicUtil.parentPointer(
					civlsource, pointer);
			SymbolicExpression unrolledArray;
			NumericExpression indexInUnrolledArray, unrolledArraySize;

			eval = evaluator.dereference(civlsource, state, process, parentPtr,
					false);
			state = eval.state;
			array = eval.value;
			// ------Unrolling the array pointed by the parent pointer.
			// Note: Since data in bundle is guaranteed to be in the form of a
			// 1-d array, unrolling the receiver array can make things easier.
			unrolledArray = symbolicUtil.arrayUnrolling(state, process, array,
					civlsource);
			unrolledArraySize = universe.length(unrolledArray);
			indexInUnrolledArray = this.getIndexInUnrolledArray(state, process,
					pointer, unrolledArraySize, civlsource);
			unrolledArray = this.oneDimenAssign(state, process, unrolledArray,
					indexInUnrolledArray, data, civlsource);
			eval.state = state;
			eval.value = symbolicUtil.arrayCasting(state, process,
					unrolledArray, array.type(), civlsource);
			return eval;

		} else {
			// ------If the pointer points to a memory space or an array.
			eval = evaluator.dereference(civlsource, state, process, pointer,
					false);
			state = eval.state;
			obj = eval.value;
			if (obj.type() instanceof SymbolicArrayType) {
				SymbolicExpression objArray = symbolicUtil.arrayUnrolling(
						state, process, obj, civlsource);

				objArray = this.oneDimenAssign(state, process, objArray, zero,
						data, civlsource);
				eval.state = state;
				eval.value = symbolicUtil.arrayCasting(state, process,
						objArray, obj.type(), civlsource);
				return eval;
			} else {
				claim = universe.equals(dataSize, one);
				if (reasoner.isValid(claim)) {
					eval.state = state;
					eval.value = universe.arrayRead(data, zero);
					return eval;
				} else {
					throw new CIVLExecutionException(ErrorKind.OUT_OF_BOUNDS,
							Certainty.PROVEABLE, "Bundle Unpack", process,
							civlsource);
				}
			}
		}
	}

	/**
	 * Computes the new index for an array element reference after the
	 * referenced array being unrolled.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param oriPointer
	 *            The pointer to the original array(before unrolling) or array
	 *            element.
	 * @param unrolledArraySize
	 *            The size of the unrolled array.
	 * @param civlsource
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public NumericExpression getIndexInUnrolledArray(State state,
			String process, SymbolicExpression oriPointer,
			NumericExpression unrolledArraySize, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		ReferenceExpression ref = symbolicUtil.getSymRef(oriPointer);

		if (ref.isArrayElementReference()) {
			SymbolicExpression parentPtr = symbolicUtil.parentPointer(
					civlsource, oriPointer);
			SymbolicExpression array = evaluator.dereference(civlsource, state,
					process, parentPtr, false).value;
			NumericExpression arrayLength = universe.length(array);
			NumericExpression chunkLength;
			NumericExpression newIndex;
			NumericExpression arrayIdx = universe.integer(symbolicUtil
					.getArrayIndex(civlsource, oriPointer));

			chunkLength = universe.divide(unrolledArraySize, arrayLength);
			newIndex = universe.multiply(arrayIdx, chunkLength);
			return newIndex;
		} else
			return zero;
	}

	/**
	 * Assigns a sequence of data (in the form of a one dimensional array, not
	 * the same "sequence" as a type of CIVL-C language) to an one dimensional
	 * array.
	 * 
	 * Pre-Condition: Parameters "array" and "data" are both one dimensional
	 * array.
	 * 
	 * Note: This function can be public if any other module want use it.
	 * 
	 * Implementation details: Since multiple dimensional arrays are represented
	 * in CIVL as nested one dimensional arrays, the one dimensional assignment
	 * is an operation only on the most outer array in those nested arrays.
	 * Note: So it's recommended to passing one dimensional arrays as parameters
	 * for "array" and "data".
	 * 
	 * e.g. For an array "a"<code>int a[2][2];</code> assigned by data
	 * <code>int b = [2][4];</code>, it finally will return a[2][4];
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param array
	 *            The array is going to be assigned by a set of data.
	 * @param data
	 *            The data is going to be assigned to an array
	 * @param civlsource
	 * @return The array after assignment.
	 */
	private SymbolicExpression oneDimenAssign(State state, String process,
			SymbolicExpression array, NumericExpression arrayIndex,
			SymbolicExpression data, CIVLSource civlsource) {
		NumericExpression arrayLength, dataLength, arrayFreeSpace;
		BooleanExpression claim;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		arrayLength = universe.length(array);
		dataLength = universe.length(data);
		if ((array.type() instanceof SymbolicArrayType)
				&& (data.type() instanceof SymbolicArrayType)) {
			arrayFreeSpace = universe.subtract(arrayLength, arrayIndex);

			claim = universe.and(universe.equals(zero, arrayIndex),
					universe.equals(arrayFreeSpace, dataLength));
			if (reasoner.isValid(claim)) {
				return data;
			} else {
				NumericExpression i = universe.zeroInt();

				claim = universe.lessThan(i, dataLength);
				while (reasoner.isValid(claim)) {
					SymbolicExpression element = universe.arrayRead(data, i);

					try {
						array = universe.arrayWrite(array, arrayIndex, element);
					} catch (SARLException e) {
						throw new SARLException("Array assignment out of bound");
					}
					// update
					i = universe.add(i, one);
					arrayIndex = universe.add(arrayIndex, one);
					claim = universe.lessThan(i, dataLength);
				}
				return array;
			}
		} else
			throw new CIVLInternalException("arguments: " + array + " and "
					+ data + "must be an one dimensional array.\n", civlsource);
	}

	/* ********************************************************************* */
}
