package edu.udel.cis.vsl.civl.semantics.contract;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiEvaluator;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.ContractConditionGenerator;
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

public class ContractEvaluator extends CommonEvaluator implements Evaluator {

	private ContractConditionGenerator conditionGenerator;

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
		conditionGenerator = new CommonContractConditionGenerator(modelFactory,
				stateFactory, symbolicUtil, symbolicAnalyzer, loader,
				memUnitFactory, errorLogger, config);
		this.FINALIZED = universe.integer(2);
		this.INITIALIZED = universe.oneInt();
	}

	public ContractConditionGenerator contractConditionGenerator() {
		return this.conditionGenerator;
	}

	/*****************
	 * Derivation Section
	 * 
	 * @throws UnsatisfiablePathConditionException
	 ****************/
	public Evaluation deriveExpression(State state, int pid,
			Expression expression) throws UnsatisfiablePathConditionException {
		return conditionGenerator.deriveExpression(state, pid, expression);
	}

	public Triple<State, SymbolicExpression, SymbolicExpression> deriveMPICollectiveTitle(
			State state, int pid, String process,
			MPICollectiveBehavior collective, Scope functionOuter)
			throws UnsatisfiablePathConditionException {
		LibmpiEvaluator mpiEvaluator;

		try {
			mpiEvaluator = (LibmpiEvaluator) libLoader.getLibraryEvaluator(
					"mpi", this, modelFactory, symbolicUtil, symbolicAnalyzer);
			return mpiEvaluator.deriveMPICollectiveBlockTitle(state, pid,
					process, collective.communicator(),
					collective.mpiCommunicationPattern(), functionOuter);
		} catch (LibraryLoaderException e) {
			e.printStackTrace();
			return null;
		}
	}

	@Deprecated
	public State verifyMPICollectiveBehavior(State state, int pid,
			String process, MPICollectiveBehavior collective,
			CIVLFunction function) throws UnsatisfiablePathConditionException {
		LibmpiEvaluator mpiEvaluator;

		try {
			mpiEvaluator = (LibmpiEvaluator) libLoader.getLibraryEvaluator(
					"mpi", this, modelFactory, symbolicUtil, symbolicAnalyzer);
			for (Expression ensures : collective.ensurances()) {
				Evaluation eval;

				// TODO: move to LibmpiEvaluator
				eval = evaluate(state, pid, ensures);
				state = eval.state;
			}
		} catch (LibraryLoaderException e) {
			e.printStackTrace();
			return null;
		}
		return state;
	}

	/***********************
	 * Evaluating section
	 * 
	 * @throws UnsatisfiablePathConditionException
	 ************************/
	@Override
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		String process = state.getProcessState(pid).name() + "(id = " + pid
				+ ")";

		if (expression.expressionKind().equals(
				ExpressionKind.MPI_CONTRACT_EXPRESSION)) {
			return evaluateMPIContractExpression(state, pid, process,
					(MPIContractExpression) expression);
		} else
			return super.evaluate(state, pid, expression);
	}

	/*
	 * Methods here do regular evaluation on expressions. Some methods are
	 * overridded because of some different semantics for contracts
	 */
	@Override
	public Evaluation pointerAdd(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression pointer,
			NumericExpression offset)
			throws UnsatisfiablePathConditionException {
		return conditionGenerator.pointerAdd(state, pid, process, expression,
				pointer, offset);
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

	private Evaluation evaluateMPIContractExpression(State state, int pid,
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
			// TODO: complete me
			return null;
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
		if (lowInt == null || highInt == null)
			throw new CIVLUnimplementedFeatureException(
					"Reasoning on $range with non-concrete parameters.");
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
	 * Override for pointers: In a contract system, a pointer will be
	 * initialized as a symbolic constant "XP[sid, vid]", where "sid" is the
	 * lexical scope id. A pointer will be initialized only if it's a parameter
	 * of the verifying function or it is a global variable.
	 */
	@Override
	protected Evaluation evaluateInitialValue(State state, int pid,
			InitialValueExpression expression)
			throws UnsatisfiablePathConditionException {
		CIVLType exprType = expression.getExpressionType();

		if (exprType.isPointerType()) {
			return new Evaluation(state,
					conditionGenerator.initializePointer(expression.variable()));
		} else
			return super.evaluateInitialValue(state, pid, expression);
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
}
