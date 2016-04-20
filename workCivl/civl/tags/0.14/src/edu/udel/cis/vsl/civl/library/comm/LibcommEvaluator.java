package edu.udel.cis.vsl.civl.library.comm;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

public class LibcommEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	private NumericExpression minusOne = universe.integer(-1);
	private NumericExpression minusTwo = universe.integer(-2);

	/* **************************** Constructors *************************** */

	public LibcommEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				libEvaluatorLoader);
	}

	/* ********************* Methods from LibraryEvaluator ******************* */

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
		default:
			guard = universe.trueExpression();
		}
		return new Evaluation(state, guard);
	}

	/* *************************** Private Methods ************************* */

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
	 * (message(predicate1)) ||...|| predicate4 && (message(predicate4))) TODO:
	 * explain message(...)
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
		// TODO: if source and tag is concrete, we just need to call
		// getAllMatchingSources() once.
		guard = dequeueGuardGenerator(civlsource, state, predicates, gcomm,
				source, dest, tag);
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
			hasMsg = universe.bool(!getAllMatchingSources(state, predicate,
					gcomm, source, dest, tag, civlsource).isEmpty());
			guardComponent = universe.and(predicate, hasMsg);
			if (guardComponent.isTrue())
				return universe.trueExpression();
			guard = universe.or(guard, guardComponent);
		} while (predIter.hasNext());

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
	List<SymbolicExpression> getAllMatchingSources(State state,
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
		// TODO: explain me!!!
		if (sourceNumber != null && sourceNumber.intValue() == -1)
			isWildcardSource = true;
		if (tagNumber != null && tagNumber.intValue() == -2)
			isWildcardTag = true;
		buf = universe.tupleRead(gcomm, universe.intObject(2));
		// non-wild card source and tag
		if (!isWildcardSource && !isWildcardTag) {
			BooleanExpression iterLTQueueLengthClaim;
			NumericExpression iter = zero;

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
		}// non-wild card source and wild card tag
		else if (!isWildcardSource && isWildcardTag) {
			bufRow = universe.arrayRead(buf, (NumericExpression) source);
			queue = universe.arrayRead(bufRow, (NumericExpression) dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = universe.tupleRead(queue, zeroObject);
			if (reasoner.isValid(universe.lessThan(zero,
					(NumericExpression) queueLength)))
				results.add(source);
		} // wild card source and non-wild card tag
		else if (isWildcardSource && !isWildcardTag) {
			NumericExpression nprocs = (NumericExpression) universe.tupleRead(
					gcomm, zeroObject);
			NumericExpression iter = universe.zeroInt();
			BooleanExpression iterLTnprocsClaim = universe.lessThan(iter,
					nprocs);

			// TODO: non-concrete nprocs
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

			// TODO: non-concrete nprocs
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
