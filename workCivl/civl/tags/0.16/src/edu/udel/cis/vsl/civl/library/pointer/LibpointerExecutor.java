package edu.udel.cis.vsl.civl.library.pointer;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class LibpointerExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	public LibpointerExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
	}

	/**
	 * Executes a system function call, updating the left hand side expression
	 * with the returned value if any.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param call
	 *            The function call statement to be executed.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeWork(State state, int pid, CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		LHSExpression lhs;
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		numArgs = call.arguments().size();
		name = call.function().name();
		lhs = call.lhs();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = call.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (name.name()) {
		case "$contains":
			state = executeContains(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$copy":
			state = executeCopy(state, pid, process, arguments, argumentValues,
					call.getSource());
			break;
		case "$equals":
			state = executeEquals(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$translate_ptr":
			state = executeTranslatePointer(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$leaf_node_ptrs":
			state = executeLeafNodePointers(state, pid, process, arguments,
					argumentValues, call.getSource());
			break;
		default:
			throw new CIVLUnimplementedFeatureException("the function " + name
					+ " of library pointer.cvh", call.getSource());
		}
		state = stateFactory.setLocation(state, pid, call.target());
		return state;
	}

	/**
	 * Copies the references to the leaf nodes of obj to the given array
	 * <p>
	 * obj:pointer to type T' whose leaf node types are all type T <br>
	 * array: pointer to array of pointer to type T
	 * 
	 * void $leaf_node_ptrs(void *array, void *obj);
	 * 
	 * incomplete array type not supporte at this point
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeLeafNodePointers(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		// TODO check null or invalid pointers.
		CIVLType objectType = symbolicAnalyzer.typeOfObjByPointer(
				arguments[1].getSource(), state, argumentValues[1]);
		List<ReferenceExpression> leafs = this.evaluator
				.leafNodeReferencesOfType(arguments[1].getSource(), state, pid,
						objectType);
		List<SymbolicExpression> leafPointers = new ArrayList<>();
		SymbolicExpression objectPointer = argumentValues[1];
		SymbolicExpression result;

		for (ReferenceExpression ref : leafs) {
			leafPointers.add(this.symbolicUtil.setSymRef(objectPointer, ref));
		}
		result = universe.array(modelFactory.pointerSymbolicType(),
				leafPointers);
		state = this.primaryExecutor.assign(source, state, process,
				argumentValues[0], result);
		return state;
	}

	private State executeContains(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression first = argumentValues[0], second = argumentValues[1];

		// TODO checks errors: when first pointer is null; when either pointer
		// is invalid pointer.
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs,
					symbolicUtil.contains(first, second));
		return state;
	}

	private State executeCopy(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression left = argumentValues[0];
		SymbolicExpression right = argumentValues[1];
		Evaluation eval;
		CIVLSource sourceLeft = arguments[0].getSource();
		CIVLSource sourceRight = arguments[1].getSource();

		if (symbolicUtil.isNullPointer(left)
				|| symbolicUtil.isNullPointer(right)) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.DEREFERENCE, Certainty.PROVEABLE, process,
					"The arguments of $copy() must both be non-null pointers.\n"
							+ "actual value of first argument: "
							+ symbolicAnalyzer.symbolicExpressionToString(
									sourceLeft, state, left)
							+ "\n"
							+ "actual value of second argument: "
							+ symbolicAnalyzer.symbolicExpressionToString(
									sourceRight, state, right),
					symbolicAnalyzer.stateToString(state), source);

			this.errorLogger.reportError(err);
			return state;
		} else {
			SymbolicExpression rightValue;
			CIVLType objTypeLeft = symbolicAnalyzer.typeOfObjByPointer(
					sourceLeft, state, left);
			CIVLType objTypeRight = symbolicAnalyzer.typeOfObjByPointer(
					sourceRight, state, right);

			if (!objTypeLeft.equals(objTypeRight)) {
				CIVLExecutionException err = new CIVLExecutionException(
						ErrorKind.DEREFERENCE,
						Certainty.PROVEABLE,
						process,
						"The objects pointed to by the two given pointers of $copy() "
								+ "must have the same type.\n"
								+ "actual type of the object of the first argument: "
								+ objTypeLeft
								+ "\n"
								+ "actual type of the object of the second argument: "
								+ objTypeRight,
						symbolicAnalyzer.stateToString(state), source);

				this.errorLogger.reportError(err);
				return state;
			}
			eval = evaluator.dereference(sourceRight, state, process, right,
					false);
			state = eval.state;
			rightValue = eval.value;
			state = primaryExecutor.assign(source, state, process, left,
					rightValue);
		}
		return state;
	}

	/**
	 * are the object pointed to equal?
	 * 
	 * _Bool $equals(void *x, void *y);
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeEquals(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression first, second;
		Evaluation eval = evaluator.dereference(arguments[0].getSource(),
				state, process, argumentValues[0], false);
		int invalidArg = -1;

		state = eval.state;
		first = eval.value;
		eval = evaluator.dereference(arguments[1].getSource(), state, process,
				argumentValues[1], false);
		state = eval.state;
		second = eval.value;
		if (!symbolicUtil.isInitialized(first))
			invalidArg = 0;
		else if (!symbolicUtil.isInitialized(second))
			invalidArg = 1;
		if (invalidArg != -1) {
			SymbolicExpression invalidValue = invalidArg == 0 ? first : second;
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.UNDEFINED_VALUE, Certainty.PROVEABLE, process,
					"The object that "
							+ arguments[invalidArg]
							+ " points to is undefined, which has the value "
							+ symbolicAnalyzer.symbolicExpressionToString(
									arguments[invalidArg].getSource(), state,
									invalidValue),
					symbolicAnalyzer.stateToString(state),
					arguments[invalidArg].getSource());

			this.errorLogger.reportError(err);
		}
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs,
					universe.equals(first, second));
		return state;
	}

	/**
	 * Translates a pointer into one object to a pointer into a different object
	 * with similar structure.
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeTranslatePointer(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer = argumentValues[0];
		SymbolicExpression objPtr = argumentValues[1];

		if (symbolicUtil.isNullPointer(pointer)
				|| symbolicUtil.isNullPointer(objPtr)) {
			if (lhs != null)
				state = this.primaryExecutor.assign(state, pid, process, lhs,
						symbolicUtil.nullPointer());
		} else {
			ReferenceExpression reference = this.symbolicUtil
					.referenceOfPointer(pointer);
			SymbolicExpression newPointer = symbolicUtil.extendPointer(objPtr,
					reference);
			CIVLSource objSource = arguments[1].getSource();
			int dyscopeId = symbolicUtil.getDyscopeId(objSource, newPointer);
			int vid = symbolicUtil.getVariableId(objSource, newPointer);
			SymbolicExpression objValue = state
					.getVariableValue(dyscopeId, vid);

			reference = (ReferenceExpression) symbolicUtil
					.getSymRef(newPointer);
			if (!symbolicUtil.isValidRefOf(reference, objValue)) {
				CIVLExecutionException err = new CIVLExecutionException(
						ErrorKind.OTHER,
						Certainty.PROVEABLE,
						process,
						"The second argument of $translate_ptr() "
								+ symbolicAnalyzer.symbolicExpressionToString(
										objSource, state, objPtr)
								+ " doesn't have a compatible type hierarchy as the first argument "
								+ symbolicAnalyzer.symbolicExpressionToString(
										arguments[0].getSource(), state,
										pointer),
						symbolicAnalyzer.stateToString(state), source);

				this.errorLogger.reportError(err);
				return state;
			}
			if (lhs != null)
				state = this.primaryExecutor.assign(state, pid, process, lhs,
						newPointer);
		}
		return state;
	}

}
