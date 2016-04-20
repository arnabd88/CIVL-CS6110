package edu.udel.cis.vsl.civl.semantics.contract;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiEvaluator;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.common.CommonEvaluator;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

/**
 * This class extends {@link CommonEvaluator} with contracts evaluating
 * semantics.
 * <p>
 * This is a summary of the extension or over-written for contracts system:
 * General section:
 * <ol>
 * <li>\valid(pointer set): denotes a set of pointers P are valid, i.e. for all
 * pointer p in P, p is dereferable.</li>
 * <li>\remote(variable, process): expresses a remote expression. A remote
 * expression evaluates to the evaluation of the variable on the process. NOTE
 * there are two restrictions on use of remote expressions:
 * <ul>
 * <li>Remote expressions currently cannot be used at requirements of function
 * contracts</li>
 * <li>All variables v appear in the process expression of a remote expression
 * must be declared inside the verifying function body. The verifying function
 * is the function owns the contracts. Or v can only be constants.</li>
 * </ul>
 * These two restrictions are suppose to avoid the difficulty of building the
 * start state of a verifying function and more importantly non-sense remote
 * expressions.</li>
 * <li>dereference: The dereferencing operation must be able to recognize
 * weather undereferable pointers are concrete and not guaranteed to be valid.</li>
 * </ol>
 * 
 * MPI section: Evaluation of MPI contract expressions and collective evaluation
 * see {@link LibmpiEvaluator}
 * </p>
 * 
 * @author ziqingluo
 *
 */
public class ContractEvaluator extends CommonEvaluator implements Evaluator {
	/**
	 * FINALIZED flag value for MPI system status variable
	 */
	public final NumericExpression FINALIZED;
	/**
	 * INITIALIZED flag value for MPI system status variable
	 */
	public final NumericExpression INITIALIZED;

	public ContractEvaluator(ModelFactory modelFactory,
			StateFactory stateFactory, LibraryEvaluatorLoader loader,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			MemoryUnitFactory memUnitFactory, CIVLErrorLogger errorLogger,
			CIVLConfiguration config) {
		super(modelFactory, stateFactory, loader, symbolicUtil,
				symbolicAnalyzer, memUnitFactory, errorLogger, config);
		this.FINALIZED = universe.integer(2);
		this.INITIALIZED = universe.oneInt();
	}

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		ExpressionKind kind = expression.expressionKind();

		if (kind.equals(ExpressionKind.MPI_CONTRACT_EXPRESSION)) {
			int processIdentifier = state.getProcessState(pid).identifier();
			String process = "p" + processIdentifier + " (id = " + pid + ")";

			return evaluateMPIContractExpression(state, pid, process,
					(MPIContractExpression) expression);
		} else
			return super.evaluate(state, pid, expression);
	}

	@Override
	protected Evaluation evaluateBinary(State state, int pid, String process,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		BINARY_OPERATOR operator = expression.operator();

		if (operator.equals(BINARY_OPERATOR.REMOTE))
			return evaluateRemoteExpression(state, pid, process, expression);
		else
			return super.evaluateBinary(state, pid, process, expression);
	}

	/**
	 * 
	 * The evaluating on a remote accessing expression follows the semantics:
	 * <p>
	 * A {@link BINARY_OPERATOR#REMOTE} operation takes two operands: left hand
	 * side operand represents a variable v and the right hand side operand
	 * represents a process p.
	 *
	 * The whole expression evaluates to the evaluation of the variable v on
	 * process p. It requires that at the evaluation time, v must be visible at
	 * the location where the control of p is. Such a restriction indicates that
	 * remote expression can hardly be used at other lexical locations than
	 * contract expression. The use of remote expressions in contract see
	 * {@link ContractEvaluator}
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param expression
	 *            The remote expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateRemoteExpression(State state, int pid,
			String process, BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		SymbolicExpression symProc, value = null;
		int remotePid;
		int dyscopeId;
		int vid = -1;
		Expression processExpr = expression.right();
		VariableExpression variableExpr = (VariableExpression) expression
				.left();
		Variable variable = null;

		eval = this.evaluate(state, pid, processExpr);
		state = eval.state;
		symProc = eval.value;
		// If the process expression is not a NumericExpression, report the
		// error.
		if (!(symProc instanceof NumericExpression)) {
			errorLogger.logSimpleError(expression.getSource(), state, process,
					symbolicAnalyzer.stateToString(state), ErrorKind.OTHER,
					"The right-hand side expression of a remote access "
							+ " must be a numeric expression.");
			throw new UnsatisfiablePathConditionException();
		}
		remotePid = ((IntegerNumber) universe
				.extractNumber((NumericExpression) symProc)).intValue();
		dyscopeId = state.getProcessState(remotePid).getDyscopeId();
		variable = variableExpr.variable();
		while (dyscopeId != -1) {
			Scope scope1 = state.getDyscope(dyscopeId).lexicalScope();

			if (scope1.containsVariable(variable.name().name())) {
				vid = scope1.variable(variable.name()).vid();
				break;
			}
			dyscopeId = state.getParentId(dyscopeId);
		}
		if (dyscopeId != -1 && vid != -1)
			value = state.getVariableValue(dyscopeId, vid);
		else {
			this.errorLogger.logSimpleError(expression.getSource(), state,
					process, symbolicAnalyzer.stateToString(state),
					ErrorKind.OTHER,
					"Remote access failure: The remote variable "
							+ variableExpr.toString()
							+ "doesn't reachable by the remote process:"
							+ remotePid);
			throw new UnsatisfiablePathConditionException();
		}
		if (value == null)
			throw new UnsatisfiablePathConditionException();
		eval = new Evaluation(state, value);
		return eval;
	}

	/**
	 * TODO: Is this function useful ?
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param collective
	 * @param function
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public Triple<State, SymbolicExpression, SymbolicExpression> deriveMPICollectiveTitle(
			State state, int pid, String process,
			MPICollectiveBehavior collective, CIVLFunction function)
			throws UnsatisfiablePathConditionException {
		LibmpiEvaluator mpiEvaluator;

		try {
			mpiEvaluator = (LibmpiEvaluator) libLoader.getLibraryEvaluator(
					"mpi", this, modelFactory, symbolicUtil, symbolicAnalyzer);
			return mpiEvaluator.deriveMPICollectiveBlockTitle(state, pid,
					process, collective, function);
		} catch (LibraryLoaderException e) {
			e.printStackTrace();
			return null;
		}
	}

	/**
	 * Override for adding contract specific operations evaluating
	 * implementations.
	 */
	@Override
	protected Evaluation evaluateUnary(State state, int pid,
			UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		UNARY_OPERATOR unaryOp = expression.operator();
		String process = state.getProcessState(pid).name() + "(id = " + pid
				+ ")";

		switch (unaryOp) {
		case VALID:
			return this.evaluateValidOperatorExpression(state, pid, process,
					expression);
		default:
			return super.evaluateUnary(state, pid, expression);
		}
	}

	/**
	 * Evaluating a {@link UnaryExpression} whose operator is
	 * {@link UNARY_OPERATOR#VALID} to true or false
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param expression
	 *            The {@link UnaryExpression}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateValidOperatorExpression(State state, int pid,
			String process, UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		PointerSetExpression mem = (PointerSetExpression) expression.operand();
		Evaluation eval;
		SymbolicExpression pointer, range;
		NumericExpression low, high;
		IntegerNumber lowInt, highInt;
		Reasoner reasoner;
		boolean result = true;

		eval = this.evaluate(state, pid, mem.getBasePointer());
		state = eval.state;
		pointer = eval.value;
		// range must be concrete if it isn't null:
		if (mem.getRange() != null) {
			eval = evaluate(state, pid, mem.getRange());
			state = eval.state;
			range = eval.value;
			low = symbolicUtil.getLowOfRegularRange(range);
			high = symbolicUtil.getHighOfRegularRange(range);
		} else {
			low = universe.zeroInt();
			high = universe.zeroInt();
		}
		reasoner = universe.reasoner(state.getPathCondition());
		lowInt = (IntegerNumber) reasoner.extractNumber(low);
		highInt = (IntegerNumber) reasoner.extractNumber(high);
		if (lowInt == null || highInt == null) {
			// TODO: here may not be necessary. Pointers should already be
			// concretized at this point, checking valid with non-concrete range
			// can only happened in derivation on requirements.
			return new Evaluation(state, universe.trueExpression());
			// throw new CIVLUnimplementedFeatureException(
			// "Attempt to evaluate $range object with non-concrete parameters.");
		}
		if (pointer.operator().equals(SymbolicOperator.TUPLE)) {
			if (lowInt.intValue() > highInt.intValue())
				throw new CIVLSyntaxException(
						"A range in \\valid must has a step with value one.");
			for (int i = lowInt.intValue(); i <= highInt.intValue(); i++) {
				eval = evaluatePointerAdd(state, process, pointer,
						universe.integer(i), false, expression.getSource()).left;
				state = eval.state;
				if (symbolicAnalyzer.isDerefablePointer(state, eval.value).right != ResultType.YES) {
					errorLogger.logSimpleError(expression.getSource(), state,
							process, symbolicAnalyzer.stateToString(state),
							ErrorKind.CONTRACT, mem.getBasePointer() + " + "
									+ i
									+ " can not to proved as a valid pointer.");
					result = false;
				}
			}
			return new Evaluation(state, universe.bool(result));
		}
		return new Evaluation(state, universe.bool(false));
	}

	/**
	 * Override for handling non-concrete symbolic pointers: The current policy
	 * for symbolic pointers does not allow dereferencing a symbolic pointer.
	 */
	@Override
	protected Evaluation evaluateDereference(State state, int pid,
			String process, DereferenceExpression expression)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer;
		Evaluation eval;

		eval = this.evaluate(state, pid, expression.pointer());
		state = eval.state;
		pointer = eval.value;
		if (pointer.operator().equals(SymbolicOperator.LAMBDA)) {
			errorLogger
					.logSimpleError(expression.getSource(), state, process,
							symbolicAnalyzer.stateToString(state),
							ErrorKind.CONTRACT,
							"Attempt to dereference a pointer which cannot be proved as a valid pointer.");
			throw new UnsatisfiablePathConditionException();
		} else
			return super.evaluateDereference(state, pid, process, expression);
	}

	/**
	 * Loading MPI library evaluator to evaluate MPI Contract expressions. see
	 * {@link LibmpiEvaluator#evaluateMPIContractExpression(State, int, String, MPIContractExpression)}
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param expression
	 *            The {@link MPIContractExpression}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateMPIContractExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		LibmpiEvaluator mpiEvaluator;

		try {
			mpiEvaluator = (LibmpiEvaluator) this.libLoader
					.getLibraryEvaluator("mpi", this, modelFactory,
							symbolicUtil, this.symbolicAnalyzer);
			return mpiEvaluator.evaluateMPIContractExpression(state, pid,
					process, expression);
		} catch (LibraryLoaderException e) {
			this.errorLogger.logSimpleError(expression.getSource(), state,
					process, symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY,
					"unable to load the library evaluator for the library "
							+ "mpi" + " for the MPI expression " + expression);
			throw new UnsatisfiablePathConditionException();
		}
	}
}
