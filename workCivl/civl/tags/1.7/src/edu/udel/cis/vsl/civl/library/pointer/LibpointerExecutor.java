package edu.udel.cis.vsl.civl.library.pointer;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

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
	public State execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement, functionName);
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
	private State executeWork(State state, int pid, CallOrSpawnStatement call,
			String functionName) throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		LHSExpression lhs;
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";
		boolean checkUndefinedValue = true;

		numArgs = call.arguments().size();
		lhs = call.lhs();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		if (functionName.equals("$is_derefable_pointer"))
			checkUndefinedValue = false;
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = call.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i],
					checkUndefinedValue);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (functionName) {
		case "$apply":
			state = executeApply(state, pid, process, arguments,
					argumentValues, call.getSource());
			break;
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
		case "$assert_equals":
			state = executeAssertEquals(state, pid, process, call, arguments,
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
		case "$is_identity_ref":
			state = executeIsIdentityRef(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$leaf_nodes_equal_to":
			state = execute_leaf_nodes_equal_to(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$has_leaf_node_equal_to":
			state = execute_has_leaf_node_equal_to(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$set_default":
			state = executeSetDefault(state, pid, process, arguments,
					argumentValues, call.getSource());
			break;
		case "$set_leaf_nodes":
			state = execute_set_leaf_nodes(state, pid, process, arguments,
					argumentValues, call.getSource());
			break;
		case "$is_derefable_pointer":
			state = execute_is_valid_pointer(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$pointer_add":
			state = executePointer_add(state, pid, process, arguments,
					argumentValues, lhs, call.getSource());
			break;
		default:
			throw new CIVLUnimplementedFeatureException("the function " + name
					+ " of library pointer.cvh", call.getSource());
		}
		state = stateFactory.setLocation(state, pid, call.target(),
				call.lhs() != null);
		return state;
	}

	/**
	 * <pre>
	 * updates the leaf nodes of a status variable to the default value 0
	 * 
	 * void $set_default(void *status);
	 * </pre>
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
	private State executeSetDefault(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		// TODO Auto-generated method stub
		CIVLType objectTypeByPointer = symbolicAnalyzer.typeOfObjByPointer(
				arguments[0].getSource(), state, argumentValues[0]);
		SymbolicExpression value;

		// TODO assert objectTypeByPointer.isScalarType()
		if (objectTypeByPointer.isBoolType())
			value = this.falseValue;
		else if (objectTypeByPointer.isIntegerType())
			value = this.zero;
		else if (objectTypeByPointer.isRealType())
			value = universe.rational(0);
		else if (objectTypeByPointer.isCharType())
			value = universe.character((char) 0);
		else if (objectTypeByPointer.isPointerType())
			value = symbolicUtil.nullPointer();
		else
			throw new CIVLUnimplementedFeatureException("Argument of "
					+ objectTypeByPointer + " type for $set_default()", source);
		state = this.primaryExecutor.assign(source, state, process,
				argumentValues[0], value);
		return state;
	}

	/**
	 * <pre>
	 * applies the operation op on obj1 and obj2 and stores the result 
	 * void $apply(void *obj1, $operation op, void *obj2, void *result);
	 * </pre>
	 * 
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
	private State executeApply(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		// TODO Auto-generated method stub
		SymbolicExpression obj1, obj2, result;
		Evaluation eval;
		int operator;

		eval = this.evaluator.dereference(arguments[0].getSource(), state,
				process, arguments[0], argumentValues[0], false);
		state = eval.state;
		obj1 = eval.value;
		eval = this.evaluator.dereference(arguments[2].getSource(), state,
				process, arguments[2], argumentValues[2], false);
		state = eval.state;
		obj2 = eval.value;
		operator = this.symbolicUtil.extractInt(arguments[1].getSource(),
				(NumericExpression) argumentValues[1]);
		result = this.applyCIVLOperator(state, process, obj1, obj2,
				this.translateOperator(operator), source);
		state = this.primaryExecutor.assign(source, state, process,
				argumentValues[3], result);
		return state;
	}

	private State execute_is_valid_pointer(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression result = this.symbolicAnalyzer.isDerefablePointer(
				state, argumentValues[0]).left;

		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					result);
		return state;
	}

	/**
	 * 
	 returns true iff at least one leaf nodes of the given object equal to the
	 * given value
	 * 
	 * _Bool $has_leaf_node_equal_to(void *obj, int value);
	 * 
	 * @throws UnsatisfiablePathConditionException
	 */

	private State execute_has_leaf_node_equal_to(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		CIVLType objectType = symbolicAnalyzer.typeOfObjByPointer(
				arguments[1].getSource(), state, argumentValues[0]);
		List<ReferenceExpression> leafs = this.evaluator
				.leafNodeReferencesOfType(arguments[0].getSource(), state, pid,
						objectType);
		List<SymbolicExpression> leafPointers = new ArrayList<>();
		SymbolicExpression objectPointer = argumentValues[0];
		Evaluation eval;
		SymbolicExpression result = falseValue;

		for (ReferenceExpression ref : leafs)
			leafPointers.add(this.symbolicUtil.setSymRef(objectPointer, ref));
		for (SymbolicExpression leafPtr : leafPointers) {
			eval = this.evaluator.dereference(source, state, process, null,
					leafPtr, false);
			state = eval.state;
			if (universe.equals(eval.value, argumentValues[1]).isTrue()) {
				result = trueValue;
				break;
			}
		}
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					result);
		return state;
	}

	/**
	 * _Bool $leaf_nodes_equal_to(void *obj, int value);
	 * 
	 * @throws UnsatisfiablePathConditionException
	 */

	private State execute_leaf_nodes_equal_to(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		CIVLType objectType = symbolicAnalyzer.typeOfObjByPointer(
				arguments[1].getSource(), state, argumentValues[0]);
		List<ReferenceExpression> leafs = this.evaluator
				.leafNodeReferencesOfType(arguments[0].getSource(), state, pid,
						objectType);
		List<SymbolicExpression> leafPointers = new ArrayList<>();
		SymbolicExpression objectPointer = argumentValues[0];
		Evaluation eval;
		SymbolicExpression result = trueValue;

		for (ReferenceExpression ref : leafs)
			leafPointers.add(this.symbolicUtil.setSymRef(objectPointer, ref));
		for (SymbolicExpression leafPtr : leafPointers) {
			eval = this.evaluator.dereference(source, state, process, null,
					leafPtr, false);
			state = eval.state;
			if (universe.equals(eval.value, argumentValues[1]).isFalse()) {
				result = falseValue;
				break;
			}
		}
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					result);
		return state;
	}

	/**
	 * 
	 updates the leaf nodes of the given objects to with the given integer
	 * value
	 * 
	 * void $set_leaf_nodes(void *obj, int value);
	 * 
	 * @throws UnsatisfiablePathConditionException
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
	private State execute_set_leaf_nodes(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		CIVLType objectType = symbolicAnalyzer.typeOfObjByPointer(
				arguments[1].getSource(), state, argumentValues[0]);
		List<ReferenceExpression> leafs = this.evaluator
				.leafNodeReferencesOfType(arguments[0].getSource(), state, pid,
						objectType);
		List<SymbolicExpression> leafPointers = new ArrayList<>();
		SymbolicExpression objectPointer = argumentValues[0];
		// SymbolicExpression result;

		for (ReferenceExpression ref : leafs)
			leafPointers.add(this.symbolicUtil.setSymRef(objectPointer, ref));
		for (SymbolicExpression leafPtr : leafPointers)
			state = this.primaryExecutor.assign(source, state, process,
					leafPtr, argumentValues[1]);
		return state;
	}

	/**
	 * _Bool $is_identity_ref(void *obj);
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
	private State executeIsIdentityRef(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression result = falseValue, objetPointer = argumentValues[0];

		if (!symbolicUtil.isHeapPointer(objetPointer)) {
			if (symbolicUtil.getSymRef(objetPointer).isIdentityReference())
				result = trueValue;
		}
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					result);
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
		result = universe
				.array(typeFactory.pointerSymbolicType(), leafPointers);
		state = this.primaryExecutor.assign(source, state, process,
				argumentValues[0], result);
		return state;
	}

	private State executeContains(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression first = argumentValues[0], second = argumentValues[1], result;
		Pair<BooleanExpression, ResultType> checkFirst = symbolicAnalyzer
				.isDerefablePointer(state, first), checkRight = symbolicAnalyzer
				.isDerefablePointer(state, second);

		if (checkFirst.right != ResultType.YES
				|| checkRight.right != ResultType.YES)
			result = falseValue;
		else
			result = symbolicUtil.contains(first, second);
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, result);
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
			StringBuffer msg = new StringBuffer();

			msg.append("the arguments of $copy() must both be non-null pointers.\n");
			msg.append("first argument:\n");
			msg.append("    ");
			msg.append(arguments[0]);
			msg.append("    ");
			msg.append(symbolicAnalyzer.expressionEvaluation(state, pid,
					arguments[0], false).right);
			msg.append("\n    ");
			msg.append(symbolicAnalyzer.symbolicExpressionToString(sourceLeft,
					state, arguments[0].getExpressionType(), left));
			msg.append("\nsecond argument:\n");
			msg.append("    ");
			msg.append(arguments[1]);
			msg.append("    ");
			msg.append(symbolicAnalyzer.expressionEvaluation(state, pid,
					arguments[1], false).right);
			msg.append("\n    ");
			msg.append(symbolicAnalyzer.symbolicExpressionToString(sourceRight,
					state, arguments[1].getExpressionType(), right));
			this.errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.DEREFERENCE, msg.toString());
			throw new UnsatisfiablePathConditionException();
		} else {
			SymbolicExpression rightValue;
			CIVLType objTypeLeft = symbolicAnalyzer.typeOfObjByPointer(
					sourceLeft, state, left);
			CIVLType objTypeRight = symbolicAnalyzer.typeOfObjByPointer(
					sourceRight, state, right);

			if (!objTypeLeft.equals(objTypeRight)) {
				StringBuffer msg = new StringBuffer();

				msg.append("the objects pointed to by the two given pointers of $copy() "
						+ "must have the same type.\n");
				msg.append("first argument:\n");
				msg.append("    ");
				msg.append(arguments[0]);
				msg.append("\n    ");
				msg.append(symbolicAnalyzer.expressionEvaluation(state, pid,
						arguments[0], false).right);
				msg.append("\n    type of the object: ");
				msg.append(objTypeLeft);
				msg.append("\nsecond argument:\n");
				msg.append("    ");
				msg.append(arguments[1]);
				msg.append("\n    ");
				msg.append(symbolicAnalyzer.expressionEvaluation(state, pid,
						arguments[1], false).right);
				msg.append("\n    type of the object: ");
				msg.append(objTypeRight);
				this.errorLogger.logSimpleError(source, state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.DEREFERENCE, msg.toString());
				throw new UnsatisfiablePathConditionException();
			}
			eval = evaluator.dereference(sourceRight, state, process,
					arguments[1], right, false);
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
		SymbolicExpression first, second, rhs;
		Evaluation eval = evaluator.dereference(arguments[0].getSource(),
				state, process, arguments[0], argumentValues[0], false);
		int invalidArg = -1;

		state = eval.state;
		first = eval.value;
		eval = evaluator.dereference(arguments[1].getSource(), state, process,
				arguments[1], argumentValues[1], false);
		state = eval.state;
		second = eval.value;
		if (!symbolicUtil.isInitialized(first))
			invalidArg = 0;
		else if (!symbolicUtil.isInitialized(second))
			invalidArg = 1;
		if (invalidArg != -1) {
			SymbolicExpression invalidValue = invalidArg == 0 ? first : second;

			this.errorLogger.logSimpleError(
					source,
					state,
					process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.UNDEFINED_VALUE,
					"the object that "
							+ arguments[invalidArg]
							+ " points to is undefined, which has the value "
							+ symbolicAnalyzer.symbolicExpressionToString(
									arguments[invalidArg].getSource(), state,
									null, invalidValue));
			// recovery:
			rhs = this.falseValue;
		} else
			rhs = universe.equals(first, second);
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, rhs);
		return state;
	}

	/**
	 * Executing an assertion that objects pointed by two pointers are equal.
	 * The statement will have such a form:<br>
	 * <code>void $assert_equals(void *x, void *y, ...);</code>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The identifier string of the process
	 * @param arguments
	 *            Expressions of arguments
	 * @param argumentValues
	 *            Symbolic expressions of arguments
	 * @param source
	 *            CIVL source of the statement
	 * @return the new state after executing the statement
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeAssertEquals(State state, int pid, String process,
			CallOrSpawnStatement call, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression firstPtr, secondPtr;
		SymbolicExpression first, second;
		BooleanExpression claim;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		ResultType resultType;
		Evaluation eval;
		boolean firstPtrDefined, secPtrDefined, firstInit, secondInit;

		firstPtrDefined = secPtrDefined = true;
		firstInit = secondInit = true;
		firstPtr = argumentValues[0];
		secondPtr = argumentValues[1];
		if (firstPtr.operator() != SymbolicOperator.TUPLE)
			firstPtrDefined = false;
		if (secondPtr.operator() != SymbolicOperator.TUPLE)
			secPtrDefined = false;
		if (!firstPtrDefined || !secPtrDefined) {
			String msg = new String();

			if (!firstPtrDefined)
				msg += symbolicAnalyzer.symbolicExpressionToString(
						arguments[0].getSource(), state,
						arguments[0].getExpressionType(), firstPtr);
			if (!secPtrDefined) {
				msg += (!firstPtrDefined) ? ", " : "";
				msg += symbolicAnalyzer.symbolicExpressionToString(
						arguments[1].getSource(), state,
						arguments[1].getExpressionType(), secondPtr);
			}
			errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.DEREFERENCE,
					"Attempt to dereference a invalid pointer:" + msg);
			return state;
		}
		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				arguments[0], argumentValues[0], false);
		state = eval.state;
		first = eval.value;
		eval = evaluator.dereference(arguments[1].getSource(), state, process,
				arguments[1], argumentValues[1], false);
		state = eval.state;
		second = eval.value;
		if (!symbolicUtil.isInitialized(first))
			firstInit = false;
		if (!symbolicUtil.isInitialized(second))
			secondInit = false;
		if (!firstInit || !secondInit) {
			String ptrMsg = new String();
			String objMsg = new String();

			if (!firstInit) {
				ptrMsg += symbolicAnalyzer.symbolicExpressionToString(
						arguments[0].getSource(), state, null, firstPtr);
				objMsg += symbolicAnalyzer.symbolicExpressionToString(
						arguments[0].getSource(), state, null, first);
			}
			if (!secondInit) {
				String comma = (!firstInit) ? ", " : "";

				ptrMsg += comma;
				objMsg += comma;
				ptrMsg += symbolicAnalyzer.symbolicExpressionToString(
						arguments[1].getSource(), state, null, secondPtr);
				objMsg += symbolicAnalyzer.symbolicExpressionToString(
						arguments[1].getSource(), state, null, second);
			}
			this.errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.UNDEFINED_VALUE, "the object that " + ptrMsg
							+ " points to is undefined, which has the value "
							+ objMsg);
			return state;
		}
		claim = universe.equals(first, second);
		resultType = reasoner.valid(claim).getResultType();
		if (resultType != ResultType.YES) {
			StringBuilder message = new StringBuilder();
			String firstArg, secondArg;

			message.append("Context: ");
			message.append(reasoner.getReducedContext());
			message.append("\nAssertion voilated: ");
			message.append(call.toString());
			message.append("\nEvaluation: \n          ");
			firstArg = this.symbolicAnalyzer.symbolicExpressionToString(
					arguments[0].getSource(), state,
					arguments[0].getExpressionType(), argumentValues[0]);
			message.append(arguments[0].toString() + "=" + firstArg);
			message.append("\n          ");
			secondArg = this.symbolicAnalyzer.symbolicExpressionToString(
					arguments[1].getSource(), state,
					arguments[1].getExpressionType(), argumentValues[1]);
			message.append(arguments[1].toString() + "=" + secondArg);
			message.append("\nResult: \n          ");
			message.append(firstArg.substring(1)
					+ "="
					+ this.symbolicAnalyzer.symbolicExpressionToString(
							arguments[0].getSource(),
							state,
							((CIVLPointerType) arguments[0].getExpressionType())
									.baseType(), first));
			message.append("\n          ");
			message.append(secondArg.substring(1)
					+ "="
					+ this.symbolicAnalyzer.symbolicExpressionToString(
							arguments[1].getSource(),
							state,
							((CIVLPointerType) arguments[1].getExpressionType())
									.baseType(), second));
			state = this.reportAssertionFailure(state, pid, process,
					resultType, message.toString(), arguments, argumentValues,
					source, claim, 2);
		}
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
				this.errorLogger
						.logSimpleError(
								source,
								state,
								process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.OTHER,
								"the second argument of $translate_ptr() "
										+ symbolicAnalyzer
												.symbolicExpressionToString(
														objSource, state, null,
														objPtr)
										+ " doesn't have a compatible type hierarchy as the first argument "
										+ symbolicAnalyzer
												.symbolicExpressionToString(
														arguments[0]
																.getSource(),
														state, null, pointer));
				throw new UnsatisfiablePathConditionException();
			}
			if (lhs != null)
				state = this.primaryExecutor.assign(state, pid, process, lhs,
						newPointer);
		}
		return state;
	}

	/**
	 * Execute the
	 * <code>void * $pointer_add(const void *ptr, int offset, int type_size);</code>
	 * system function.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The string identifier of the process
	 * @param arguments
	 *            {@link Expression} of arguments
	 * @param argumentValues
	 *            {@link SymbolicExpression} of arguments
	 * @param source
	 *            CIVL source of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executePointer_add(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			LHSExpression lhs, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression ptr = argumentValues[0];
		SymbolicExpression output_ptr;
		NumericExpression offset = (NumericExpression) argumentValues[1];
		NumericExpression type_size = (NumericExpression) argumentValues[2];
		// ptr_primType_size: the size of the primitive type pointed by first
		// argument, which
		// should be equal to the last argument which is the size of the
		// expected primitive type
		NumericExpression ptr_primType_size;
		CIVLType primitiveTypePointedStatic;
		SymbolicType primitiveTypePointed;
		Evaluation eval;
		BooleanExpression claim;
		Reasoner reasoner;
		ResultType resultType;

		if (!ptr.operator().equals(SymbolicOperator.TUPLE)) {
			errorLogger.logSimpleError(
					source,
					state,
					process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.DEREFERENCE,
					"$pointer_add() doesn't accept an invalid pointer:"
							+ symbolicAnalyzer.symbolicExpressionToString(
									source, state, null, ptr));
			throw new UnsatisfiablePathConditionException();
		}
		primitiveTypePointedStatic = symbolicAnalyzer.getArrayBaseType(state,
				arguments[0].getSource(), ptr);
		primitiveTypePointed = primitiveTypePointedStatic
				.getDynamicType(universe);
		ptr_primType_size = symbolicUtil.sizeof(arguments[0].getSource(),
				primitiveTypePointedStatic, primitiveTypePointed);
		if (!this.civlConfig.svcomp()) {
			claim = universe.equals(ptr_primType_size, type_size);
			reasoner = universe.reasoner(state.getPathCondition());
			resultType = reasoner.valid(claim).getResultType();
			if (!resultType.equals(ResultType.YES)) {
				this.errorLogger
						.logError(
								source,
								state,
								process,
								this.symbolicAnalyzer.stateInformation(state),
								claim,
								resultType,
								ErrorKind.POINTER,
								"the primitive type of the object pointed by input pointer:"
										+ primitiveTypePointed
										+ " must be"
										+ " consistent with the size of the"
										+ " primitive type specified at the forth argument: "
										+ type_size);
				throw new UnsatisfiablePathConditionException();
			}
		}
		eval = evaluator.evaluatePointerAdd(state, process, ptr, offset, true,
				source).left;
		state = eval.state;
		output_ptr = eval.value;
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					output_ptr);
		return state;
	}
}
