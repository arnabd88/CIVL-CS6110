package edu.udel.cis.vsl.civl.library.comm;

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
import edu.udel.cis.vsl.sarl.IF.number.Number;

public class LibcommEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	private NumericExpression minusOne = universe.integer(-1);
	private NumericExpression minusTwo = universe.integer(-2);
	private BooleanExpression trueExpr = universe.trueExpression();

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
	 * Return a boolean expression represents the guard of the function
	 * <code>$comm_dequeue(comm, source, tag)</code>. If is hard to decide
	 * weather source is wild card or not, add all possible situations into the
	 * returned guard (ditto for tag). e.g. (source is wild card -->(imply)
	 * ture) && (source is not wild card --> (imply) false)
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
		NumericExpression dest;
		BooleanExpression sourceGTEzero = trueExpr;
		BooleanExpression isAnySource = trueExpr;
		BooleanExpression isAnyTag = trueExpr;
		BooleanExpression tagGTEzero = trueExpr;
		boolean certainSrc, certainTag;
		BooleanExpression guard;
		List<BooleanExpression> predicates = new LinkedList<>();
		CIVLSource civlsource = arguments.get(0).getSource();
		Evaluation eval;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		eval = evaluator.dereference(civlsource, state, process, commHandle,
				false);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gcommHandle,
				false);
		state = eval.state;
		gcomm = eval.value;
		dest = (NumericExpression) universe.tupleRead(comm, zeroObject);
		predicates = new LinkedList<>();
		assert source instanceof NumericExpression : "Argument of source of $comm_dequeue() should be a numeric type.\n";
		if (reasoner.extractNumber((NumericExpression) source) == null) {
			sourceGTEzero = universe.lessThanEquals(zero,
					(NumericExpression) source);
			isAnySource = universe.equals(source, minusOne);
			certainSrc = false;
		} else
			certainSrc = true;
		assert tag instanceof NumericExpression : "Argument of tag of $comm_dequeue() should be a numeric type.\n";
		if (reasoner.extractNumber((NumericExpression) tag) == null) {
			tagGTEzero = universe.lessThanEquals(zero, (NumericExpression) tag);
			isAnyTag = universe.equals(tag, minusTwo);
			certainTag = false;
		} else
			certainTag = true;
		if (certainSrc && certainTag)
			predicates.add(trueExpr);
		else if (certainTag) {
			predicates.add(isAnySource);
			predicates.add(sourceGTEzero);
		} else if (certainSrc) {
			predicates.add(isAnyTag);
			predicates.add(tagGTEzero);
		} else {
			predicates.add(universe.and(isAnySource, isAnyTag));
			predicates.add(universe.and(isAnySource, tagGTEzero));
			predicates.add(universe.and(sourceGTEzero, isAnyTag));
			predicates.add(universe.and(sourceGTEzero, tagGTEzero));
		}
		guard = dequeueGuardGenerator(civlsource, state, predicates, gcomm,
				(NumericExpression) source, dest, (NumericExpression) tag);
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
			SymbolicExpression gcomm, NumericExpression source,
			NumericExpression dest, NumericExpression tag)
			throws UnsatisfiablePathConditionException {
		BooleanExpression guardComponent;
		BooleanExpression guard = universe.falseExpression();
		BooleanExpression hasMsg;
		int intSrc, intTag;
		Number numSrc, numTag;

		for (BooleanExpression predicate : predicates) {
			Reasoner reasoner;

			reasoner = universe.reasoner(universe.and(state.getPathCondition(),
					predicate));
			numSrc = reasoner.extractNumber(source);
			assert numSrc != null : "Source of a message is expected to be concrete.\n";
			assert numSrc instanceof IntegerNumber : "Source of a message must be able to cast to an IntegerNumber object.\n";
			intSrc = ((IntegerNumber) numSrc).intValue();
			numTag = reasoner.extractNumber(tag);
			assert numTag != null : "Tag of a message is expected to be concrete.\n";
			assert numTag instanceof IntegerNumber : "Tag of a message must be able to cast to an IntegerNumber object.\n";
			intTag = ((IntegerNumber) numTag).intValue();
			hasMsg = universe.bool(!getAllPossibleSources(state, reasoner,
					gcomm, intSrc, intTag, dest, civlsource).isEmpty());
			guardComponent = universe.and(predicate, hasMsg);
			if (guardComponent.isTrue())
				return universe.trueExpression();
			guard = universe.or(guard, guardComponent);
		}
		return guard;
	}

	/**
	 * Seeks all possible channels of the given communicator for all available
	 * sources whose corresponding channel (which is decided by "destination"
	 * which is the process itself and the "source") contains at least one
	 * message with a satisfied tag.
	 * 
	 * @param state
	 *            The current state
	 * @param reasoner
	 *            The reasoner used to evaluate concrete numbers
	 * @param gcomm
	 *            The symbolic expression of a global communicator object
	 * @param source
	 *            The integer type source number
	 * @param tag
	 *            The integer type tag number
	 * @param dest
	 *            The integer type destination number
	 * @param civlsource
	 * @return A list of all available sources
	 * @throws UnsatisfiablePathConditionException
	 */
	public List<NumericExpression> getAllPossibleSources(State state,
			Reasoner reasoner, SymbolicExpression gcomm, int source, int tag,
			NumericExpression dest, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression buf;
		SymbolicExpression bufRow;
		SymbolicExpression queue;
		NumericExpression queueLength;
		SymbolicExpression messages = null;
		SymbolicExpression message = null;
		NumericExpression sourceVal = universe.integer(source);
		NumericExpression tagVal = universe.integer(tag);
		List<NumericExpression> results = new LinkedList<>();

		buf = universe.tupleRead(gcomm, universe.intObject(2));
		assert (source == -1 || source >= 0) : "Message source is neither wild-card nor valid positive integer.\n";
		assert (tag == -2 || tag >= 0) : "Message tag is neither wild-card nor valid positive integer.\n";
		// non-wild card source and tag
		if (source >= 0 && tag >= 0) {
			Number numQueLength;
			int intQueLength;

			bufRow = universe.arrayRead(buf, sourceVal);
			queue = universe.arrayRead(bufRow, dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = (NumericExpression) universe.tupleRead(queue,
					zeroObject);
			numQueLength = reasoner.extractNumber(queueLength);
			assert numQueLength != null : "Length of message queue is expected to be concrete.\n";
			assert numQueLength instanceof IntegerNumber : "Length of message queue must be able to cast to an IntegerNumber object.\n";
			intQueLength = ((IntegerNumber) numQueLength).intValue();
			for (int i = 0; i < intQueLength; i++) {
				message = universe.arrayRead(messages, universe.integer(i));
				if (reasoner.isValid(universe.equals(
						universe.tupleRead(message, twoObject), tagVal))) {
					results.add(sourceVal);
					return results;
				}
			}
		}// non-wild card source and any_tag
		else if (source >= 0 && tag == -2) {
			bufRow = universe.arrayRead(buf, sourceVal);
			queue = universe.arrayRead(bufRow, dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = (NumericExpression) universe.tupleRead(queue,
					zeroObject);
			if (reasoner.isValid(universe.lessThan(zero,
					(NumericExpression) queueLength)))
				results.add(sourceVal);
			return results;
		} // any source and non-wild card tag
		else if (source == -1 && tag >= 0) {
			Number numNprocs;
			int intNumNprocs;
			Number numQueLength;
			int intNumQueLength;
			NumericExpression nprocs = (NumericExpression) universe.tupleRead(
					gcomm, zeroObject);

			numNprocs = reasoner.extractNumber(nprocs);
			assert numNprocs != null : "The number of processes in communicator is expected to be concrete.\n";
			assert numNprocs instanceof IntegerNumber : "The number of processes in communicator must be able to cast to an IntegerNumber object.\n";
			intNumNprocs = ((IntegerNumber) numNprocs).intValue();
			for (int i = 0; i < intNumNprocs; i++) {
				NumericExpression currProc = universe.integer(i);

				bufRow = universe.arrayRead(buf, currProc);
				queue = universe.arrayRead(bufRow, dest);
				messages = universe.tupleRead(queue, oneObject);
				queueLength = (NumericExpression) universe.tupleRead(queue,
						zeroObject);
				numQueLength = reasoner.extractNumber(queueLength);
				assert numQueLength != null : "Length of message queue is expected to be concrete.\n";
				assert numQueLength instanceof IntegerNumber : "Length of message queue must be able to cast to an IntegerNumber object.\n";
				intNumQueLength = ((IntegerNumber) numQueLength).intValue();
				for (int j = 0; j < intNumQueLength; j++) {
					BooleanExpression tagMatchClaim;

					message = universe.arrayRead(messages, universe.integer(j));
					tagMatchClaim = universe.equals(
							universe.tupleRead(message, twoObject), tagVal);
					if (reasoner.isValid(tagMatchClaim)) {
						results.add(currProc);
						break;
					}
				}
			}
			return results;
		} // wild card source and wild card tag
		else if (source == -1 && tag == -2) {
			Number numNprocs;
			int intNumNprocs;
			NumericExpression nprocs = (NumericExpression) universe.tupleRead(
					gcomm, zeroObject);

			numNprocs = reasoner.extractNumber(nprocs);
			assert numNprocs != null : "The number of processes in communicator is expected to be concrete.\n";
			assert numNprocs instanceof IntegerNumber : "The number of processes in communicator must be able to cast to an IntegerNumber object.\n";
			intNumNprocs = ((IntegerNumber) numNprocs).intValue();
			for (int i = 0; i < intNumNprocs; i++) {
				NumericExpression currProc = universe.integer(i);

				bufRow = universe.arrayRead(buf, currProc);
				queue = universe.arrayRead(bufRow, dest);
				messages = universe.tupleRead(queue, oneObject);
				queueLength = (NumericExpression) universe.tupleRead(queue,
						zeroObject);
				if (reasoner.isValid(universe.lessThan(zero,
						(NumericExpression) queueLength)))
					results.add(currProc);
			}
			return results;
		}
		return results;
	}
}
