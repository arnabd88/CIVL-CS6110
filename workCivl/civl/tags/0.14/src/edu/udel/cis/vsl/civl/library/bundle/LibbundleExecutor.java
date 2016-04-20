package edu.udel.cis.vsl.civl.library.bundle;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
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
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * <p>
 * Specification for bundle operations:<br>
 * The specification of bundle pack/unpack is essentially the specification of
 * get/set data from input/output arguments. Since CIVL implements multiple
 * dimensional arrays as nested arrays, assigning a set of data to a multiple
 * dimensional array will possibly involve several parts of different sub-arrays
 * inside a nested array. So the following description will note some
 * explanation of general cases for this get/set input/output arguments problem
 * which is totally irrelevant to bundle pack/unpack.
 * </p>
 * 
 * 
 * $bundle $bundle_pack(void *ptr, int size):<br>
 * <p>
 * Putting the whole or part of the object pointed by the first argument into
 * returned a bundle object.<br>
 * the first argument "ptr" is a pointer to the object part of which is going to
 * be assigned to the returned bundle type object. The second argument specifies
 * the size of the object pointed by the first argument. Here size means the
 * size of the data type times the the number of the elements of such data type
 * which are consisted of the data object will be packed in bundle.<br>
 * Note: For general cases, if some input argument, which happens to be a
 * pointer, has a specified data type, it's unnecessary to give the size unless
 * the function is just expecting part of the object pointed.
 * </p>
 * 
 * void $bundle_unpack($bundle bundle, void *ptr):
 * <p>
 * Extracting the whole data from a given bundle and assigning it to another
 * object pointed by the second argument. The pre-condition is the receiving
 * object must be able to contain the whole data object.<br>
 * The first argument is the bundle object which will be extracted. The second
 * argument is a pointer to receiving object. The pre-condition mentioned above
 * is defined as: If the receiving object has a compatible data type of itself
 * or elements of it with the data itself or elements of the data inside the
 * bundle and the size of the object (sometime it's just part of the object
 * because of different positions pointed by the pointer) is greater than or
 * equal to data in bundle, it's able to contain the whole data object. <br>
 * Note: For general setting output arguments cases, this precondition should
 * also hold. The only thing different is the data in bundle here can be data
 * from anywhere(Obviously general cases are irrelevant with bundle stuff).<br>
 * </p>
 * 
 * 
 */

public class LibbundleExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	LibbundleEvaluator libevaluator;

	/* **************************** Constructors *************************** */

	public LibbundleExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
		libevaluator = new LibbundleEvaluator(name, evaluator, modelFactory,
				symbolicUtil, symbolicAnalyzer, libEvaluatorLoader);
	}

	/* ******************** Methods from LibraryExecutor ******************* */

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
	}

	/* ************************** Private Methods ************************** */

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
		case "$bundle_pack":
			state = executeBundlePack(state, pid, process,
					(CIVLBundleType) call.function().returnType(), lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$bundle_size":
			state = executeBundleSize(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$bundle_unpack":
			state = executeBundleUnpack(state, pid, process, arguments,
					argumentValues, call.getSource());
			break;
		case "$bundle_unpack_apply":
			state = executeBundleUnpackApply(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		}
		state = stateFactory.setLocation(state, pid, call.target());
		return state;
	}

	/**
	 * Returns the size of a bundle.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param civlSource
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeBundleSize(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource civlSource)
			throws UnsatisfiablePathConditionException {
		SymbolicObject arrayObject;
		SymbolicExpression array;
		NumericExpression size;

		assert arguments.length == 1;
		assert argumentValues[0].operator() == SymbolicOperator.UNION_INJECT;
		arrayObject = argumentValues[0].argument(1);
		assert arrayObject instanceof SymbolicExpression;
		array = (SymbolicExpression) arrayObject;
		size = symbolicUtil.sizeof(civlSource, array.type());
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, size);
		return state;
	}

	/**
	 * Creates a bundle from the memory region specified by ptr and size,
	 * copying the data into the new bundle:
	 * 
	 * <code>$bundle $bundle_pack(void *ptr, int size);</code>
	 * 
	 * Copies the data out of the bundle into the region specified:
	 * 
	 * <code>void $bundle_unpack($bundle bundle, void *ptr, int size);</code>
	 * 
	 * Pre-Condition : The size of the object pointed by the given address
	 * should larger than or equal to the other parameter "size".<br>
	 * Post-Condition: The data in bundle is in the form of an unrolled one
	 * dimensional array.<br>
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param process
	 *            The information of the process.
	 * @param bundleType
	 *            The bundle type of the model.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeBundlePack(State state, int pid, String process,
			CIVLBundleType bundleType, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer = argumentValues[0];
		NumericExpression size = (NumericExpression) argumentValues[1];
		NumericExpression count = null;
		SymbolicType elementType;
		SymbolicUnionType symbolicBundleType;
		SymbolicExpression arrayInBundle = null;
		SymbolicExpression bundle = null;
		IntObject elementTypeIndexObj;
		Evaluation eval;
		int elementTypeIndex;

		if (pointer.operator() != SymbolicOperator.CONCRETE) {
			errorLogger.reportError(new CIVLExecutionException(
					ErrorKind.POINTER, Certainty.CONCRETE, process,
					"Attempt to read/write a invalid pointer type variable",
					arguments[1].getSource()));
			return state;
		}
		if (pointer.type().typeKind() != SymbolicTypeKind.TUPLE) {
			throw new CIVLUnimplementedFeatureException(
					"string literals in message passing function calls,",
					source);
		}
		// check if size is zero
		if (size.isZero()) {
			// if size is 0 then just ignore the pointer. The pointer could be
			// NULL, or even invalid. The result is still a bundle of size 0.
			symbolicBundleType = bundleType.getDynamicType(universe);
			elementTypeIndex = 0;
			elementTypeIndexObj = universe.intObject(0);
			elementType = bundleType.getElementType(elementTypeIndex);
			arrayInBundle = universe.emptyArray(elementType);
			bundle = universe.unionInject(symbolicBundleType,
					elementTypeIndexObj, arrayInBundle);
		} else if (!size.isZero()
				&& symbolicUtil.getDyscopeId(source, pointer) == -1
				&& symbolicUtil.getVariableId(source, pointer) == -1) {
			throw new CIVLSyntaxException(
					"Packing a NULL message with size larger than 0", source);
		} else {
			Reasoner reasoner = universe.reasoner(state.getPathCondition());
			BooleanExpression claim;

			elementType = symbolicAnalyzer.getFlattenedArrayElementType(state,
					arguments[0].getSource(), pointer).getDynamicType(universe);
			count = universe.divide(size,
					symbolicUtil.sizeof(arguments[1].getSource(), elementType));
			// If count == 1, directly dereferencing the pointer to get the
			// first non-array element.
			claim = universe.equals(count, one);
			if (!reasoner.isValid(claim)) {
				try {
					eval = libevaluator.getDataFrom(state, process, pointer,
							count, false, arguments[0].getSource());
					state = eval.state;
					arrayInBundle = eval.value;
				} catch (CIVLInternalException | CIVLExecutionException e) {
					CIVLExecutionException err = new CIVLExecutionException(
							ErrorKind.OUT_OF_BOUNDS, Certainty.PROVEABLE,
							process,
							"Packing data with count: "
									+ count
									+ "from pointer: "
									+ symbolicAnalyzer
											.symbolicExpressionToString(source,
													state, pointer), source);
					errorLogger.reportError(err);
				} catch (Exception e) {
					CIVLExecutionException err = new CIVLExecutionException(
							ErrorKind.OTHER, Certainty.PROVEABLE, process,
							"Bundle pack failed", source);
					errorLogger.reportError(err);
					return state;
				}
			} else {
				eval = evaluator.dereference(source, state, process, pointer,
						true);
				if (eval.value.type() instanceof SymbolicArrayType) {
					SymbolicExpression arraySubObj = eval.value;

					while (((SymbolicArrayType) arraySubObj.type())
							.elementType() instanceof SymbolicArrayType)
						arraySubObj = universe.arrayRead(arraySubObj, zero);
					arrayInBundle = symbolicAnalyzer.getSubArray(arraySubObj,
							zero, one, state, process, source);
				} else
					arrayInBundle = universe.array(elementType,
							Arrays.asList(eval.value));
				state = eval.state;
			}
			assert (arrayInBundle != null);
			symbolicBundleType = bundleType.getDynamicType(universe);
			elementTypeIndex = bundleType.getIndexOf(universe
					.pureType(elementType));
			elementTypeIndexObj = universe.intObject(elementTypeIndex);
			bundle = universe.unionInject(symbolicBundleType,
					elementTypeIndexObj, arrayInBundle);
		}
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, bundle);
		return state;
	}

	/**
	 * Copies the data out of the bundle into the region specified:
	 * 
	 * void $bundle_unpack($bundle bundle, void *ptr); <br>
	 * 
	 * Pre-Condition : The data in bundle is in the form of an falttened one
	 * dimensional array.<br>
	 * 
	 * @see{executeBunldePack :post-condition.<br>
	 * 
	 * 
	 * @author Ziqing Luo
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeBundleUnpack(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression bundle = argumentValues[0];
		SymbolicExpression pointer = argumentValues[1];
		SymbolicExpression targetObject = null;
		SymbolicExpression bufPointer = null;
		Evaluation eval;
		Pair<Evaluation, SymbolicExpression> eval_and_pointer;

		// checking if pointer is valid
		if (pointer.operator() != SymbolicOperator.CONCRETE) {
			errorLogger.reportError(new CIVLExecutionException(
					ErrorKind.POINTER, Certainty.CONCRETE, process,
					"Attempt to read/write an uninitialized variable by the pointer "
							+ pointer, arguments[1].getSource()));
			return state;
		}
		try {
			eval_and_pointer = libevaluator.bundleUnpack(state, process,
					(SymbolicExpression) bundle.argument(1), pointer, source);
			eval = eval_and_pointer.left;
			// bufPointer is the pointer to targetObj which may be the ancestor
			// of the original pointer.
			bufPointer = eval_and_pointer.right;
			state = eval.state;
			// targetObject is the object will be assigned to the output
			// argument.
			targetObject = eval.value;
		} catch (CIVLInternalException | CIVLExecutionException e) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.OUT_OF_BOUNDS, Certainty.PROVEABLE, process,
					"Unpacking data from bundle to pointer: "
							+ symbolicAnalyzer.symbolicExpressionToString(
									arguments[1].getSource(), state, pointer),
					source);

			errorLogger.reportError(err);
			return state;
		} catch (Exception e) {
			// Out of bound exception will be throw inside the bundleUnpack
			// function when an array write fails.
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.INTERNAL, Certainty.PROVEABLE, process,
					"Bundle unpacking failed", source);

			errorLogger.reportError(err);
			return state;
		}
		// If it's assigned to an array or an object
		if (bufPointer != null && targetObject != null)
			state = primaryExecutor.assign(source, state, process, bufPointer,
					targetObject);
		else
			throw new CIVLInternalException("Cannot complete unpack", source);

		return state;
	}

	/**
	 * bundle unpack then do an operation. This method corresponding to the
	 * CIVL-C function:
	 * <code>$bundle_unpack_apply($bundle bundle, void * buf, int count, $operation op);</code>
	 * Bundle contains the first operand which is going to be used in the
	 * operation. The pointer "buf" points to the object stores the second
	 * operand which is going to be used in the operation.
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param pid
	 *            The pid of the process
	 * @param process
	 *            The identifier of the process
	 * @param arguments
	 *            The expression of arguments of the CIVL-C function
	 *            <code>$bundle_unpack_apply($bundle bundle, void * buf, int count, $operation op);</code>
	 * @param argumentValues
	 *            The symbolic expression of arguments of the CIVL-C function
	 *            <code>$bundle_unpack_apply($bundle bundle, void * buf, int count, $operation op);</code>
	 * @param source
	 *            The civl source of this statement
	 * @return the state after execution.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeBundleUnpackApply(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression bundle = argumentValues[0];
		SymbolicExpression pointer = argumentValues[1];
		SymbolicExpression secOperand = null;
		SymbolicExpression data = null;
		SymbolicExpression dataElement = null;
		SymbolicExpression secOperandElement = null;
		SymbolicExpression assignPtr = null;
		SymbolicExpression opRet = null; // result after applying one operation
		NumericExpression count = (NumericExpression) argumentValues[2];
		NumericExpression i = zero;
		NumericExpression operation = (NumericExpression) argumentValues[3];
		BooleanExpression pathCondition = state.getPathCondition();
		BooleanExpression claim;
		Reasoner reasoner = universe.reasoner(pathCondition);
		CIVLOperator CIVL_Op;
		Evaluation eval = null;
		Pair<Evaluation, SymbolicExpression> eval_and_pointer;

		// Checking if pointer is valid.
		if (pointer.operator() != SymbolicOperator.CONCRETE) {
			errorLogger.reportError(new CIVLExecutionException(
					ErrorKind.POINTER, Certainty.CONCRETE, process,
					"Attempt to read/write a invalid pointer type variable",
					arguments[1].getSource()));
			return state;
		}
		// Obtain data form bundle
		data = (SymbolicExpression) bundle.argument(1);
		// Checking if data is null
		if (data.isNull() || data == null)
			return state;
		// In executor, operation must be concrete.
		// Translate operation
		CIVL_Op = CIVLOperator.values()[((IntegerNumber) reasoner
				.extractNumber(operation)).intValue()];
		// Get the second operand from pointer

		eval = libevaluator.getDataFrom(state, process, pointer, count, false,
				source);
		state = eval.state;
		secOperand = eval.value;
		// If count is non-concrete
		if (reasoner.extractNumber(count) == null) {
			NumericSymbolicConstant index = (NumericSymbolicConstant) universe
					.symbolicConstant(universe.stringObject("i"),
							universe.integerType());
			SymbolicExpression arrayEleFunc, lambdaFunc, newArray;
			SymbolicType elementType;
			SymbolicCompleteArrayType newArrayType;

			// TODO: move civlOp to super class
			// TODO: new name for civlOperation
			arrayEleFunc = this.applyCIVLOperator(state, process,
					(NumericExpression) universe.arrayRead(data, index),
					(NumericExpression) universe.arrayRead(secOperand, index),
					CIVL_Op, source);
			lambdaFunc = universe.lambda(index, arrayEleFunc);
			elementType = ((SymbolicArrayType) data.type()).elementType();
			newArrayType = universe.arrayType(elementType, count);
			newArray = universe.arrayLambda(newArrayType, lambdaFunc);
			eval_and_pointer = libevaluator.setDataFrom(state, process,
					pointer, count, newArray, false, source);
			eval = eval_and_pointer.left;
			assignPtr = eval_and_pointer.right;
			state = eval.state;
			state = primaryExecutor.assign(source, state, process, assignPtr,
					eval.value);
			return state;
		}
		try {
			i = zero;
			claim = universe.lessThan(i, count);

			while (reasoner.isValid(claim)) {
				dataElement = universe.arrayRead(data, i);
				secOperandElement = universe.arrayRead(secOperand, i);
				opRet = this.applyCIVLOperator(state, process, dataElement,
						secOperandElement, CIVL_Op, source);
				secOperand = universe.arrayWrite(secOperand, i, opRet);
				i = universe.add(i, one);
				claim = universe.lessThan(i, count);
			}

			eval_and_pointer = libevaluator.setDataFrom(state, process,
					pointer, count, secOperand, false, source);
			eval = eval_and_pointer.left;
			assignPtr = eval_and_pointer.right;
			state = eval.state;
		} catch (SARLException e) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.OUT_OF_BOUNDS, Certainty.PROVEABLE, process,
					"Operands of CIVL Operation out of bound at index: "
							+ symbolicAnalyzer.symbolicExpressionToString(
									source, state, i),
					symbolicAnalyzer.stateToString(state), source);

			errorLogger.reportError(err);
			return state;
		}
		assert (assignPtr != null) : "Unknown bug in CIVL";
		assert (eval != null) : "Unknown bug in CIVL";
		state = primaryExecutor.assign(source, state, process, assignPtr,
				eval.value);
		return state;
	}
}
