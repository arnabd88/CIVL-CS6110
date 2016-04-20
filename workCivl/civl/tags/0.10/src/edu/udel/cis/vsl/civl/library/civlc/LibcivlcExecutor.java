package edu.udel.cis.vsl.civl.library.civlc;

import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.library.CommonLibraryExecutor;
import edu.udel.cis.vsl.civl.library.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.Singleton;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression.ReferenceKind;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * Implementation of the execution for system functions declared civlc.h.
 * 
 * @author siegel
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibcivlcExecutor extends CommonLibraryExecutor implements
		LibraryExecutor {

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of the library executor for civlc.h.
	 * 
	 * @param primaryExecutor
	 *            The executor for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param enablePrintf
	 *            If printing is enabled for the printf function.
	 * @param modelFactory
	 *            The model factory of the system.
	 */
	public LibcivlcExecutor(Executor primaryExecutor, PrintStream output,
			boolean enablePrintf, ModelFactory modelFactory) {
		super(primaryExecutor, output, enablePrintf, modelFactory);
	}

	/* ******************** Methods from LibraryExecutor ******************* */

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
	}

	@Override
	public State initialize(State state) {
		return state;
	}

	@Override
	public String name() {
		return "civlc";
	}

	@Override
	public State wrapUp(State state) {
		return state;
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Creates a bundle from the memory region specified by ptr and size,
	 * copying the data into the new bundle:
	 * 
	 * $bundle $bundle_pack(void *ptr, int size);
	 * 
	 * Copies the data out of the bundle into the region specified:
	 * 
	 * void $bundle_unpack($bundle bundle, void *ptr, int size);
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
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
	private State executeBundlePack(State state, int pid,
			CIVLBundleType bundleType, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		Expression pointerExpr = arguments[0];
		SymbolicExpression pointer = argumentValues[0];
		NumericExpression size = (NumericExpression) argumentValues[1];
		SymbolicType elementType;
		SymbolicType pureElementType;
		SymbolicUnionType symbolicBundleType;
		int index;
		IntObject indexObj;
		SymbolicExpression array;
		SymbolicExpression bundle;

		if (pointer.type().typeKind() != SymbolicTypeKind.TUPLE) {
			throw new CIVLUnimplementedFeatureException(
					"string literals in message passing function calls,",
					source);
		}
		elementType = evaluator.referencedType(source, state, pointer);
		pureElementType = universe.pureType(elementType);
		symbolicBundleType = bundleType.getDynamicType(universe);
		index = bundleType.getIndexOf(pureElementType);
		indexObj = universe.intObject(index);
		array = getArrayFromPointer(state, pointerExpr, pointer, size, source);
		bundle = universe.unionInject(symbolicBundleType, indexObj, array);
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, lhs, bundle);
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
	private State executeBundleSize(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource civlSource) throws UnsatisfiablePathConditionException {
		SymbolicObject arrayObject;
		SymbolicExpression array;
		NumericExpression size;

		assert arguments.length == 1;
		assert argumentValues[0].operator() == SymbolicOperator.UNION_INJECT;
		arrayObject = argumentValues[0].argument(1);
		assert arrayObject instanceof SymbolicExpression;
		array = (SymbolicExpression) arrayObject;
		size = evaluator.sizeof(civlSource, array.type());
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, lhs, size);
		return state;
	}

	/**
	 * Copies the data out of the bundle into the region specified:
	 * 
	 * void $bundle_unpack($bundle bundle, void *ptr, int size);
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
	private State executeBundleUnpack(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression bundle = argumentValues[0];
		SymbolicExpression pointer = argumentValues[1];
		ReferenceExpression symRef = evaluator.getSymRef(pointer);
		ReferenceKind kind = symRef.referenceKind();
		SymbolicExpression array = (SymbolicExpression) bundle.argument(1);
		NumericExpression length = universe.length(array);
		BooleanExpression pathCondition = state.getPathCondition();
		BooleanExpression zeroLengthClaim = universe.equals(length, zero);
		Reasoner reasoner = universe.reasoner(pathCondition);
		ResultType zeroLengthValid = reasoner.valid(zeroLengthClaim)
				.getResultType();

		assert bundle.operator() == SymbolicOperator.UNION_INJECT;
		if (zeroLengthValid == ResultType.YES) {
			return state;
		} else {
			BooleanExpression oneLengthClaim = universe.equals(length, one);
			ResultType oneLengthValid = reasoner.valid(oneLengthClaim)
					.getResultType();

			if (oneLengthValid == ResultType.YES) {
				SymbolicExpression element = universe.arrayRead(array, zero);

				state = primaryExecutor.assign(source, state, pointer, element);
				return state;
			} else {
				// if pointer is to element 0 of an array and lengths are equal,
				// just assign the whole array
				// else try to get concrete length, and iterate making
				// assignment
				if (kind == ReferenceKind.ARRAY_ELEMENT) {
					NumericExpression pointerIndex = ((ArrayElementReference) symRef)
							.getIndex();
					SymbolicExpression parentPointer = evaluator.parentPointer(
							source, pointer);
					Evaluation eval = evaluator.dereference(source, state,
							parentPointer);
					SymbolicExpression targetArray = eval.value;
					BooleanExpression claim;

					state = eval.state;
					pathCondition = state.getPathCondition();
					claim = universe.and(
							universe.equals(pointerIndex, zero),
							universe.equals(length,
									universe.length(targetArray)));
					if (reasoner.isValid(claim)) {
						state = primaryExecutor.assign(source, state,
								parentPointer, array);

						return state;
					} else {
						IntegerNumber concreteLength = (IntegerNumber) reasoner
								.extractNumber(length);

						if (concreteLength != null) {
							int lengthInt = concreteLength.intValue();

							for (int i = 0; i < lengthInt; i++) {
								NumericExpression sourceIndex = universe
										.integer(i);
								NumericExpression targetIndex = universe.add(
										pointerIndex, sourceIndex);

								try {
									SymbolicExpression element = universe
											.arrayRead(array,
													universe.integer(i));

									targetArray = universe.arrayWrite(
											targetArray, targetIndex, element);
								} catch (SARLException e) {
									throw new CIVLStateException(
											ErrorKind.OUT_OF_BOUNDS,
											Certainty.CONCRETE,
											"Attempt to write beyond array bound: index="
													+ targetIndex, state,
											source);
								}
							}
							state = primaryExecutor.assign(source, state,
									parentPointer, targetArray);
							return state;
						}
					}
				}
			}
		}
		throw new CIVLInternalException("Cannot complete unpack", source);
	}

	/**
	 * Creates a new global communicator object and returns a handle to it. The
	 * global communicator will have size communication places. The global
	 * communicator defines a communication "universe" and encompasses message
	 * buffers and all other components of the state associated to
	 * message-passing. The new object will be allocated in the given scope.
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
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeGcommCreate(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression gcomm;
		SymbolicExpression nprocs = argumentValues[1];
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression isInit;
		SymbolicExpression isInitArray;
		SymbolicExpression buf;
		SymbolicExpression bufRow;
		SymbolicExpression queueLength = universe.integer(0);
		SymbolicExpression emptyQueue;
		SymbolicExpression emptyMessages;
		LinkedList<SymbolicExpression> emptyMessagesComponents = new LinkedList<SymbolicExpression>();
		LinkedList<SymbolicExpression> isInitComponents = new LinkedList<SymbolicExpression>();
		LinkedList<SymbolicExpression> queueComponents = new LinkedList<SymbolicExpression>();
		LinkedList<SymbolicExpression> bufRowComponents = new LinkedList<SymbolicExpression>();
		LinkedList<SymbolicExpression> bufComponents = new LinkedList<SymbolicExpression>();
		List<SymbolicExpression> gcommComponents = new LinkedList<SymbolicExpression>();
		int int_nprocs;
		Model model = state.getScope(0).lexicalScope().model();
		CIVLType queueType = model.queueType();
		CIVLType messageType = model.mesageType();
		CIVLType gcommType = model.gcommType();
		SymbolicType dynamicQueueType = queueType.getDynamicType(universe);
		SymbolicType dynamicMessageType = messageType.getDynamicType(universe);
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_nprocs = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) nprocs);

		if (number_nprocs != null)
			int_nprocs = number_nprocs.intValue();
		else
			throw new CIVLInternalException(
					"Cannot extract concrete int value for gcomm size",
					arguments[1]);
		// isInit component
		isInit = universe.bool(false);
		for (int i = 0; i < int_nprocs; i++) {
			isInitComponents.add(isInit);
		}
		isInitArray = universe.array(isInit.type(), isInitComponents);
		// buf component
		emptyMessages = universe.array(dynamicMessageType,
				emptyMessagesComponents);
		queueComponents.add(queueLength);
		queueComponents.add(emptyMessages);
		assert dynamicQueueType instanceof SymbolicTupleType;
		emptyQueue = universe.tuple((SymbolicTupleType) dynamicQueueType,
				queueComponents);
		for (int i = 0; i < int_nprocs; i++) {
			bufRowComponents.add(emptyQueue);
		}
		bufRow = universe.array(dynamicQueueType, bufRowComponents);
		for (int i = 0; i < int_nprocs; i++) {
			bufComponents.add(bufRow);
		}
		buf = universe.array(bufRow.type(), bufComponents);
		gcommComponents.add(nprocs);
		gcommComponents.add(isInitArray);
		gcommComponents.add(buf);
		gcomm = universe.tuple(
				(SymbolicTupleType) gcommType.getDynamicType(universe),
				gcommComponents);
		state = primaryExecutor.malloc(source, state, pid, lhs,
				scopeExpression, scope, gcommType, gcomm);
		return state;
	}

	/**
	 * Creates a new local communicator object and returns a handle to it. The
	 * new communicator will be affiliated with the specified global
	 * communicator. This local communicator handle will be used as an argument
	 * in most message-passing functions. The place must be in [0,size-1] and
	 * specifies the place in the global communication universe that will be
	 * occupied by the local communicator. The local communicator handle may be
	 * used by more than one process, but all of those processes will be viewed
	 * as occupying the same place. Only one call to $comm_create may occur for
	 * each gcomm-place pair. The new object will be allocated in the given
	 * scope.
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
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCommCreate(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression gcommHandle = argumentValues[1];
		SymbolicExpression place = argumentValues[2];
		SymbolicExpression gcomm;
		SymbolicExpression comm;
		SymbolicExpression isInitArray;
		LinkedList<SymbolicExpression> commComponents = new LinkedList<SymbolicExpression>();
		CIVLSource civlsource = arguments[0].getSource();
		Model model = state.getScope(0).lexicalScope().model();
		CIVLType commType = model.commType();
		Evaluation eval;

		eval = this.evaluator.dereference(civlsource, state, gcommHandle);
		state = eval.state;
		gcomm = eval.value;
		isInitArray = universe.tupleRead(gcomm, oneObject);
		assert universe.arrayRead(isInitArray, (NumericExpression) place)
				.equals(universe.bool(false));
		isInitArray = universe.arrayWrite(isInitArray,
				(NumericExpression) place, universe.bool(true));
		gcomm = universe.tupleWrite(gcomm, oneObject, isInitArray);
		state = this.primaryExecutor.assign(civlsource, state, gcommHandle,
				gcomm);
		// builds comm
		commComponents.add(place);
		commComponents.add(gcommHandle);
		comm = universe.tuple(
				(SymbolicTupleType) commType.getDynamicType(universe),
				commComponents);
		state = this.primaryExecutor.malloc(civlsource, state, pid, lhs,
				scopeExpression, scope, commType, comm);
		return state;
	}

	/**
	 * Returns the size (number of places) in the global communicator associated
	 * to the given comm.
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
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCommSize(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		SymbolicExpression nprocs;
		CIVLSource civlsource = arguments[0].getSource();
		Evaluation eval;

		eval = evaluator.dereference(civlsource, state, commHandle);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, gcommHandle);
		state = eval.state;
		gcomm = eval.value;
		nprocs = universe.tupleRead(gcomm, zeroObject);
		if (lhs != null) {
			state = this.primaryExecutor.assign(state, pid, lhs, nprocs);
		}
		return state;
	}

	/**
	 * Returns true iff a matching message exists in the communication universe
	 * specified by the comm. A message matches the arguments if the destination
	 * of the message is the place of the comm, and the sources and tags match.
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
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCommProbe(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		SymbolicExpression source = argumentValues[1];
		SymbolicExpression tag = argumentValues[2];
		SymbolicExpression dest;
		SymbolicExpression message;
		boolean isFind = false;
		CIVLSource civlsource = arguments[0].getSource();
		Evaluation eval;

		eval = evaluator.dereference(civlsource, state, commHandle);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, gcommHandle);
		state = eval.state;
		gcomm = eval.value;
		dest = universe.tupleRead(comm, zeroObject);
		message = this.getMatchedMessageFromGcomm(pid, gcomm, source, dest,
				tag, civlsource);
		if (message != null)
			isFind = true;
		if (lhs != null) {
			state = this.stateFactory.setVariable(state,
					((VariableExpression) lhs).variable(), pid,
					universe.bool(isFind));
		}
		return state;
	}

	/**
	 * Finds the first matching message and returns it without modifying the
	 * communication universe. If no matching message exists, returns a message
	 * with source, dest, and tag all negative.
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
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCommSeek(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		SymbolicExpression source = argumentValues[1];
		SymbolicExpression dest;
		SymbolicExpression tag = argumentValues[2];
		SymbolicExpression message;
		CIVLSource civlsource = arguments[0].getSource();
		Evaluation eval;

		eval = evaluator.dereference(civlsource, state, commHandle);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, gcommHandle);
		state = eval.state;
		gcomm = eval.value;
		dest = universe.tupleRead(comm, zeroObject);
		message = this.getMatchedMessageFromGcomm(pid, gcomm, source, dest,
				tag, civlsource);
		if (message == null) {
			message = this.getEmptyMessage(state);
		}
		if (lhs != null) {
			state = this.stateFactory.setVariable(state,
					((VariableExpression) lhs).variable(), pid, message);
		}
		return state;
	}

	/**
	 * Finds the first matching message, removes it from the communicator, and
	 * returns the message
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
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCommDequeue(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		CIVLSource civlsource = arguments[0].getSource();
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression newMessage = null;
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		SymbolicExpression source = argumentValues[1];
		SymbolicExpression tag = argumentValues[2];
		SymbolicExpression dest;
		SymbolicExpression buf;
		SymbolicExpression bufRow = null;
		SymbolicExpression queue = null;
		SymbolicExpression queueLength = null;
		SymbolicExpression messages = null;
		Evaluation eval;
		int int_queueLength = -1;
		int int_source;
		int int_tag;
		int MessageIndexInMessagesArray = -1;

		eval = evaluator.dereference(civlsource, state, commHandle);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, gcommHandle);
		state = eval.state;
		gcomm = eval.value;
		buf = universe.tupleRead(gcomm, universe.intObject(2));
		dest = universe.tupleRead(comm, zeroObject);
		int_source = evaluator.extractInt(civlsource,
				(NumericExpression) source);
		int_tag = evaluator.extractInt(civlsource, (NumericExpression) tag);
		buf = universe.tupleRead(gcomm, universe.intObject(2));
		// specific source and tag
		if (int_source >= 0 && int_tag >= 0) {
			bufRow = universe.arrayRead(buf, (NumericExpression) source);
			queue = universe.arrayRead(bufRow, (NumericExpression) dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = universe.tupleRead(queue, zeroObject);
			int_queueLength = evaluator.extractInt(civlsource,
					(NumericExpression) queueLength);
			for (int i = 0; i < int_queueLength; i++) {
				newMessage = universe.arrayRead(messages, universe.integer(i));
				if (universe.tupleRead(newMessage, universe.intObject(2))
						.equals(tag)) {
					MessageIndexInMessagesArray = i;
					break;
				} else
					newMessage = null;
			}
		}
		// remove the new message in the messages array
		assert int_queueLength >= 0;
		assert MessageIndexInMessagesArray >= 0;
		messages = universe.removeElementAt(messages,
				MessageIndexInMessagesArray);
		int_queueLength--;
		queueLength = universe.integer(int_queueLength);
		queue = universe.tupleWrite(queue, zeroObject, queueLength);
		queue = universe.tupleWrite(queue, oneObject, messages);
		bufRow = universe.arrayWrite(bufRow, (NumericExpression) dest, queue);
		buf = universe.arrayWrite(buf, (NumericExpression) source, bufRow);
		gcomm = universe.tupleWrite(gcomm, universe.intObject(2), buf);
		state = this.primaryExecutor.assign(civlsource, state, gcommHandle,
				gcomm);
		if (lhs != null) {
			state = this.primaryExecutor.assign(state, pid, lhs, newMessage);
		}
		return state;
	}

	/**
	 * Adds the message to the appropriate message queue in the communication
	 * universe specified by the comm. The source of the message must equal the
	 * place of the comm.
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
	private State executeCommEnqueue(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		CIVLSource civlsource = arguments[0].getSource();
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression newMessage = argumentValues[1];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		SymbolicExpression source;
		SymbolicExpression dest;
		SymbolicExpression buf;
		SymbolicExpression bufRow;
		SymbolicExpression queue;
		SymbolicExpression queueLength;
		SymbolicExpression messages;
		Evaluation eval;
		int int_queueLength;

		eval = evaluator.dereference(civlsource, state, commHandle);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, gcommHandle);
		state = eval.state;
		gcomm = eval.value;
		buf = universe.tupleRead(gcomm, universe.intObject(2));
		source = universe.tupleRead(newMessage, zeroObject);
		dest = universe.tupleRead(newMessage, oneObject);
		bufRow = universe.arrayRead(buf, (NumericExpression) source);
		queue = universe.arrayRead(bufRow, (NumericExpression) dest);
		queueLength = universe.tupleRead(queue, zeroObject);
		messages = universe.tupleRead(queue, oneObject);
		messages = universe.append(messages, newMessage);
		int_queueLength = evaluator.extractInt(civlsource,
				(NumericExpression) queueLength);
		int_queueLength++;
		queueLength = universe.integer(int_queueLength);
		queue = universe.tupleWrite(queue, zeroObject, queueLength);
		queue = universe.tupleWrite(queue, oneObject, messages);
		bufRow = universe.arrayWrite(bufRow, (NumericExpression) dest, queue);
		buf = universe.arrayWrite(buf, (NumericExpression) source, bufRow);
		gcomm = universe.tupleWrite(gcomm, universe.intObject(2), buf);
		state = this.primaryExecutor.assign(civlsource, state, gcommHandle,
				gcomm);
		return state;
	}

	/**
	 * $exit terminates the calling process.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The process ID of the process to be terminated.
	 * @return The state resulting from removing the specified process.
	 */
	private State executeExit(State state, int pid) {
		int atomicPID = stateFactory.processInAtomic(state);

		if (atomicPID == pid) {
			state = stateFactory.releaseAtomicLock(state);
		}
		return stateFactory.removeProcess(state, pid);
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
			state = executeBundlePack(state, pid, (CIVLBundleType) call
					.function().returnType(), lhs, arguments, argumentValues,
					call.getSource());
			break;
		case "$bundle_size":
			state = executeBundleSize(state, pid, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$bundle_unpack":
			state = executeBundleUnpack(state, pid, arguments, argumentValues,
					call.getSource());
			break;
		case "$comm_create":
			state = this.executeCommCreate(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$comm_defined":
			state = this.executeCommDefined(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$comm_dequeue":
			state = executeCommDequeue(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$comm_enqueue":
			state = executeCommEnqueue(state, pid, arguments, argumentValues);
			break;
		case "$comm_seek":
			state = this.executeCommSeek(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$comm_probe":
			state = this.executeCommProbe(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$comm_size":
			state = this.executeCommSize(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$exit":// return immediately since no transitions needed after an
			// exit, because the process no longer exists.
			return executeExit(state, pid);
		case "$comm_destroy":
		case "$gcomm_destroy":
		case "$free":
			state = executeFree(state, pid, arguments, argumentValues,
					call.getSource());
			break;
		case "$gcomm_create2":
			state = executeGcommCreate(state, pid, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$gcomm_defined":
			state = this.executeGcommDefined(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$proc_defined":
			state = this.executeProcDefined(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$proc_null":
			state = this.executeProcNull(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$scope_defined":
			state = this.executeScopeDefined(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$scope_parent":
			state = this.executeScopeParent(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "$wait":// return immediately since target location has been set.
			return executeWait(state, pid, arguments, argumentValues,
					call.getSource(), call.target());
		default:
			throw new CIVLInternalException("Unknown civlc function: " + name,
					call);
		}
		state = stateFactory.setLocation(state, pid, call.target());
		return state;
	}

	private State executeProcNull(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression nullProcess = this.modelFactory.nullProcessValue();
		Evaluation eval = evaluator.evaluate(state, pid, arguments[0]);

		state = eval.state;
		return primaryExecutor.assign(arguments[0].getSource(), state,
				eval.value, nullProcess);
	}

	/**
	 * Checks if a $comm object is defined, i.e., it doesn't point to the heap
	 * of an invalid scope, implementing the function $comm_defined($comm comm).
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param pid
	 *            The ID of the process that this computation belongs to.
	 * @param lhs
	 *            The left hand side expression of this function call.
	 * @param arguments
	 *            The static arguments of the function call.
	 * @param argumentValues
	 *            The symbolic values of the arguments of the function call
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCommDefined(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression result = this.isValidPointer(argumentValues[0]);

		if (lhs != null)
			state = primaryExecutor.assign(state, pid, lhs, result);
		return state;
	}

	/**
	 * Checks if a $gcomm object is defined, i.e., it doesn't point to the heap
	 * of an invalid scope, implementing the function $gcomm_defined($gcomm
	 * gcomm).
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param pid
	 *            The ID of the process that this computation belongs to.
	 * @param lhs
	 *            The left hand side expression of this function call.
	 * @param arguments
	 *            The static arguments of the function call.
	 * @param argumentValues
	 *            The symbolic values of the arguments of the function call
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeGcommDefined(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression result = this.isValidPointer(argumentValues[0]);

		if (lhs != null)
			state = primaryExecutor.assign(state, pid, lhs, result);
		return state;
	}

	/**
	 * Checks if a scope reference is defined, i.e., its id is non-negative.
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param pid
	 *            The ID of the process that this computation belongs to.
	 * @param lhs
	 *            The left hand side expression of this function call.
	 * @param arguments
	 *            The static arguments of the function call.
	 * @param argumentValues
	 *            The symbolic values of the arguments of the function call
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeScopeDefined(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression result = modelFactory.isScopeDefined(
				arguments[0].getSource(), argumentValues[0]);

		if (lhs != null)
			state = primaryExecutor.assign(state, pid, lhs, result);
		return state;
	}

	/**
	 * Checks if a process reference is defined, i.e., its id is non-negative.
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param pid
	 *            The ID of the process that this computation belongs to.
	 * @param lhs
	 *            The left hand side expression of this function call.
	 * @param arguments
	 *            The static arguments of the function call.
	 * @param argumentValues
	 *            The symbolic values of the arguments of the function call
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeProcDefined(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression result = modelFactory.isProcessDefined(
				arguments[0].getSource(), argumentValues[0]);

		if (lhs != null)
			state = primaryExecutor.assign(state, pid, lhs, result);
		return state;
	}

	/**
	 * Checks if a pointer is defined, i.e., it doesn't point to a memory unit
	 * of an invalid scope.
	 * 
	 * @param pointer
	 * @return
	 */
	private SymbolicExpression isValidPointer(SymbolicExpression pointer) {
		int scopeId = evaluator.getScopeId(null, pointer);

		if (scopeId >= 0)
			return universe.bool(true);
		else
			return universe.bool(false);
	}

	/**
	 * Executes lhs = $scope_parent($scope s).
	 * 
	 * @param state
	 *            The state where the computation happens.
	 * @param pid
	 *            The ID of the process that the executed function call belongs
	 *            to.
	 * @param lhs
	 *            The left hand side expression of the function call, which is
	 *            to be assigned with the return value.
	 * @param arguments
	 *            The static arguments of the function call.
	 * @param argumentValues
	 *            The symbolic expressions of the arguments of the function
	 *            call.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 *             if the assignment of the left hand side expression fails.
	 */
	private State executeScopeParent(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scopeValue = argumentValues[0];
		Expression scopeExpression = arguments[0];
		CIVLSource source = scopeExpression.getSource();
		int scopeID = modelFactory.getScopeId(source, scopeValue);
		int parentID = state.getParentId(scopeID);
		SymbolicExpression parentScope = modelFactory.scopeValue(parentID);

		if (lhs != null) {
			state = this.primaryExecutor.assign(state, pid, lhs, parentScope);
		}
		return state;
	}

	/**
	 * Executes the $wait system function call. Only enabled when the waited
	 * process has terminated.
	 * 
	 * * @param state The current state.
	 * 
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
	 * @param target
	 *            The target location of the wait function call.
	 * @return The new state after executing the function call.
	 * @return
	 */
	private State executeWait(State state, int pid, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source,
			Location target) {
		SymbolicExpression procVal = argumentValues[0];
		int joinedPid = modelFactory.getProcessId(arguments[0].getSource(),
				procVal);

		state = stateFactory.setLocation(state, pid, target);
		state = stateFactory.removeProcess(state, joinedPid);
		return state;
	}

	/**
	 * Obtains an array via a certain pointer.
	 * 
	 * @param state
	 *            The current state
	 * @param pointerExpr
	 *            The static representation of the pointer.
	 * @param pointer
	 *            The dynamic representation of the pointer.
	 * @param size
	 *            The size of the array.
	 * @param source
	 *            The source code element for error report.
	 * @return The symbolic representation of the array that the given pointer
	 *         points to.
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression getArrayFromPointer(State state,
			Expression pointerExpr, SymbolicExpression pointer,
			NumericExpression size, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression array = null;
		ReferenceExpression symRef = evaluator.getSymRef(pointer);
		ReferenceKind kind = symRef.referenceKind();
		SymbolicType elementType = evaluator.referencedType(source, state,
				pointer);
		NumericExpression elementSize = evaluator.sizeof(source, elementType);
		BooleanExpression pathCondition = state.getPathCondition();
		BooleanExpression zeroSizeClaim = universe.equals(size, zero);
		Reasoner reasoner = universe.reasoner(pathCondition);
		ResultType zeroSizeValid = reasoner.valid(zeroSizeClaim)
				.getResultType();

		if (zeroSizeValid == ResultType.YES) {
			array = universe.emptyArray(elementType);
		} else {
			BooleanExpression oneCountClaim = universe
					.equals(size, elementSize);
			ResultType oneCountValid = reasoner.valid(oneCountClaim)
					.getResultType();

			if (oneCountValid == ResultType.YES) {
				Evaluation eval = evaluator.dereference(
						pointerExpr.getSource(), state, pointer);
				SymbolicExpression element0 = eval.value;

				state = eval.state;
				pathCondition = state.getPathCondition();
				array = universe.array(elementType,
						new Singleton<SymbolicExpression>(element0));
			} else {
				BooleanExpression divisibility = universe.divides(elementSize,
						size);
				ResultType divisibilityValid = reasoner.valid(divisibility)
						.getResultType();
				NumericExpression count;

				if (divisibilityValid != ResultType.YES) {
					Certainty certainty = divisibilityValid == ResultType.MAYBE ? Certainty.MAYBE
							: Certainty.PROVEABLE;
					CIVLStateException e = new CIVLStateException(
							ErrorKind.OTHER, certainty,
							"sizeof element does not divide size argument",
							state, source);

					evaluator.reportError(e);
					pathCondition = universe.and(pathCondition, divisibility);
					state = state.setPathCondition(pathCondition);
					reasoner = universe.reasoner(pathCondition);
				}
				count = universe.divide(size, elementSize);
				switch (kind) {
				case ARRAY_ELEMENT: {
					NumericExpression startIndex = ((ArrayElementReference) symRef)
							.getIndex();
					SymbolicExpression arrayPointer = evaluator.parentPointer(
							source, pointer);
					Evaluation eval = evaluator.dereference(source, state,
							arrayPointer);
					SymbolicExpression originalArray = eval.value;
					NumericExpression endIndex = universe
							.add(startIndex, count);
					state = eval.state;
					array = evaluator.getSubArray(originalArray, startIndex,
							endIndex, state, source);
					break;
				}
				case IDENTITY:
					throw new CIVLStateException(ErrorKind.POINTER,
							Certainty.MAYBE,
							"unable to get concrete count of 0 or 1 from size",
							state, source);
				case NULL: { // size must be 0
					Certainty certainty = zeroSizeValid == ResultType.MAYBE ? Certainty.MAYBE
							: Certainty.PROVEABLE;
					CIVLStateException e = new CIVLStateException(
							ErrorKind.POINTER, certainty,
							"null pointer only valid with size 0", state,
							source);

					evaluator.reportError(e);
					pathCondition = universe.and(pathCondition, zeroSizeClaim);
					state = state.setPathCondition(pathCondition);
					reasoner = universe.reasoner(pathCondition);
					array = universe.emptyArray(elementType);
				}
				case OFFSET: {
					// either size is zero or size is 1 and offset is 0
					throw new CIVLStateException(ErrorKind.POINTER,
							Certainty.MAYBE, "possible out of bounds pointer",
							state, source);
				}
				case TUPLE_COMPONENT: {
					throw new CIVLStateException(ErrorKind.POINTER,
							Certainty.MAYBE,
							"unable to get concrete count of 0 or 1 from size",
							state, source);
				}
				case UNION_MEMBER:
					throw new CIVLInternalException("dereference union member",
							source);
				default:
					throw new CIVLInternalException("unreachable", source);
				}
			}
		}
		return array;
	}

	/**
	 * Computes matched message in the communicator.
	 * 
	 * @param pid
	 *            The process ID.
	 * @param gcomm
	 *            The dynamic representation of the communicator.
	 * @param source
	 *            The expected source.
	 * @param dest
	 *            The expected destination.
	 * @param tag
	 *            The expected tag.
	 * @param civlsource
	 *            The source code element for error report.
	 * @return The matched message, NULL if no matched message found.
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression getMatchedMessageFromGcomm(int pid,
			SymbolicExpression gcomm, SymbolicExpression source,
			SymbolicExpression dest, SymbolicExpression tag,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		SymbolicExpression buf;
		SymbolicExpression bufRow;
		SymbolicExpression queue;
		SymbolicExpression queueLength;
		SymbolicExpression messages = null;
		SymbolicExpression message = null;
		int int_source = evaluator.extractInt(civlsource,
				(NumericExpression) source);
		int int_tag = evaluator.extractInt(civlsource, (NumericExpression) tag);
		int int_queueLength;

		buf = universe.tupleRead(gcomm, universe.intObject(2));
		// specific source and tag
		if (int_source >= 0 && int_tag >= 0) {
			bufRow = universe.arrayRead(buf, (NumericExpression) source);
			queue = universe.arrayRead(bufRow, (NumericExpression) dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = universe.tupleRead(queue, zeroObject);
			int_queueLength = evaluator.extractInt(civlsource,
					(NumericExpression) queueLength);
			for (int i = 0; i < int_queueLength; i++) {
				message = universe.arrayRead(messages, universe.integer(i));
				if (universe.tupleRead(message, universe.intObject(2)).equals(
						tag))
					break;
				else
					message = null;
			}
		}
		return message;
	}

	private SymbolicExpression getEmptyMessage(State state) {
		SymbolicExpression message;
		Model model = state.getScope(0).lexicalScope().model();
		CIVLType messageType = model.mesageType();
		CIVLBundleType bundleType = model.bundleType();
		LinkedList<SymbolicExpression> emptyMessageComponents = new LinkedList<SymbolicExpression>();
		StringObject name;
		SymbolicExpression bundle;

		name = universe.stringObject("X_s" + -1 + "v" + -1);
		bundle = universe.symbolicConstant(name,
				bundleType.getDynamicType(universe));
		emptyMessageComponents.add(universe.integer(-1));
		emptyMessageComponents.add(universe.integer(-1));
		emptyMessageComponents.add(universe.integer(-1));
		emptyMessageComponents.add(bundle);
		emptyMessageComponents.add(universe.integer(-1));
		message = this.universe.tuple(
				(SymbolicTupleType) messageType.getDynamicType(universe),
				emptyMessageComponents);
		return message;
	}
}
