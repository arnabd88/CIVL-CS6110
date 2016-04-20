package edu.udel.cis.vsl.civl.library.civlc;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.err.CIVLException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.util.Singleton;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression.ReferenceKind;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * Implementation of system functions declared civlc.h.
 * 
 * <ul>
 * <li><code>$malloc</code>: since calls to this function have already been
 * translated to {@link MallocStatement}s in the model, these are handled a
 * little differently.</li>
 * <li><code>$free</code></li>
 * </ul>
 * 
 * @author siegel
 * 
 */
public class Libcivlc implements LibraryExecutor {

	private Executor primaryExecutor;

	private Evaluator evaluator;

	private SymbolicUniverse universe;

	private StateFactory stateFactory;

	private NumericExpression zero;

	private NumericExpression one;

	private IntObject zeroObject;

	private IntObject oneObject;

	// private SymbolicType bundleSymbolicType;

	public Libcivlc(Executor primaryExecutor, PrintStream output,
			boolean enablePrintf, ModelFactory modelFactory) {
		this.primaryExecutor = primaryExecutor;
		this.evaluator = primaryExecutor.evaluator();
		// this.log = evaluator.log();
		this.universe = evaluator.universe();
		this.stateFactory = evaluator.stateFactory();
		this.zero = universe.zeroInt();
		this.one = universe.oneInt();
		this.zeroObject = universe.intObject(0);
		this.oneObject = universe.intObject(1);
	}

	@Override
	public String name() {
		return "civlc";
	}

	public State executeMalloc(State state, int pid, MallocStatement statement)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = statement.getSource();
		int sid = state.getProcessState(pid).getDyscopeId();
		int index = statement.getMallocId();
		IntObject indexObj = universe.intObject(index);
		LHSExpression lhs = statement.getLHS();
		Evaluation eval;
		SymbolicExpression heapPointer;
		int heapVariableId;
		ReferenceExpression symRef;
		SymbolicExpression heapValue;
		NumericExpression mallocSize, elementSize;
		BooleanExpression pathCondition, claim;
		ResultType validity;
		NumericExpression elementCount;
		SymbolicExpression heapField;
		NumericExpression lengthExpression;
		int length; // num allocated objects in index component of heap
		StringObject newObjectName;
		SymbolicType newObjectType;
		SymbolicExpression newObject;
		SymbolicExpression firstElementPointer; // returned value

		eval = evaluator.evaluate(state, pid,
				statement.getHeapPointerExpression());
		state = eval.state;
		heapPointer = eval.value;
		eval = evaluator.dereference(source, state, heapPointer);
		state = eval.state;
		heapValue = eval.value;
		heapVariableId = evaluator.getVariableId(source, heapPointer);
		symRef = evaluator.getSymRef(heapPointer);
		if (!symRef.isIdentityReference())
			throw new CIVLException("heap used as internal structure", source);
		eval = evaluator.evaluate(state, pid, statement.getSizeExpression());
		state = eval.state;
		mallocSize = (NumericExpression) eval.value;
		eval = evaluator.evaluateSizeofType(source, state, pid,
				statement.getStaticElementType());
		state = eval.state;
		elementSize = (NumericExpression) eval.value;
		pathCondition = state.getPathCondition();
		claim = universe.divides(elementSize, mallocSize);
		validity = universe.reasoner(pathCondition).valid(claim)
				.getResultType();
		if (validity != ResultType.YES) {
			Certainty certainty = validity == ResultType.NO ? Certainty.PROVEABLE
					: Certainty.MAYBE;
			CIVLStateException e = new CIVLStateException(ErrorKind.MALLOC,
					certainty,
					"Size argument to $malloc is not multiple of element size",
					eval.state, source);

			evaluator.reportError(e);
			state = state.setPathCondition(universe.and(pathCondition, claim));
		}
		elementCount = universe.divide(mallocSize, elementSize);
		heapField = universe.tupleRead(heapValue, indexObj);
		lengthExpression = universe.length(heapField);
		length = evaluator.extractInt(source, lengthExpression);
		newObjectName = universe.stringObject("H_p" + pid + "s" + sid + "v"
				+ heapVariableId + "i" + index + "l" + length);
		newObjectType = universe.arrayType(statement.getDynamicElementType(),
				elementCount);
		newObject = universe.symbolicConstant(newObjectName, newObjectType);
		heapField = universe.append(heapField, newObject);
		heapValue = universe.tupleWrite(heapValue, indexObj, heapField);
		state = primaryExecutor.assign(source, state, heapPointer, heapValue);
		if (lhs != null) {
			symRef = universe.tupleComponentReference(symRef, indexObj);
			symRef = universe.arrayElementReference(symRef, lengthExpression);
			symRef = universe.arrayElementReference(symRef, zero);
			firstElementPointer = evaluator.setSymRef(heapPointer, symRef);
			state = primaryExecutor
					.assign(state, pid, lhs, firstElementPointer);
		}
		return state;
	}

	private Evaluation getAndCheckHeapObjectPointer(
			SymbolicExpression heapPointer, SymbolicExpression pointer,
			CIVLSource pointerSource, State state) {
		SymbolicExpression objectPointer = evaluator.getParentPointer(pointer);

		if (objectPointer != null) {
			SymbolicExpression fieldPointer = evaluator
					.getParentPointer(objectPointer);

			if (fieldPointer != null) {
				SymbolicExpression actualHeapPointer = evaluator
						.getParentPointer(fieldPointer);

				if (actualHeapPointer != null) {
					BooleanExpression pathCondition = state.getPathCondition();
					BooleanExpression claim = universe.equals(
							actualHeapPointer, heapPointer);
					ResultType valid = universe.reasoner(pathCondition)
							.valid(claim).getResultType();
					ReferenceExpression symRef;

					if (valid != ResultType.YES) {
						Certainty certainty = valid == ResultType.NO ? Certainty.PROVEABLE
								: Certainty.MAYBE;
						CIVLStateException e = new CIVLStateException(
								ErrorKind.MALLOC, certainty,
								"Invalid pointer for heap", state,
								pointerSource);

						evaluator.reportError(e);
						state = state.setPathCondition(universe.and(
								pathCondition, claim));
					}
					symRef = evaluator.getSymRef(pointer);
					if (symRef instanceof ArrayElementReference) {
						NumericExpression index = ((ArrayElementReference) symRef)
								.getIndex();

						if (index.isZero()) {
							return new Evaluation(state, objectPointer);
						}
					}

				}
			}
		}
		{
			CIVLStateException e = new CIVLStateException(ErrorKind.MALLOC,
					Certainty.PROVEABLE, "Invalid pointer for heap", state,
					pointerSource);

			evaluator.reportError(e);
			state = state.setPathCondition(universe.falseExpression());
			return new Evaluation(state, objectPointer);
		}
	}

	private int getMallocIndex(SymbolicExpression pointer) {
		// ref points to element 0 of an array:
		NTReferenceExpression ref = (NTReferenceExpression) evaluator
				.getSymRef(pointer);
		// objectPointer points to array:
		NTReferenceExpression objectPointer = (NTReferenceExpression) ref
				.getParent();
		// fieldPointer points to the field:
		TupleComponentReference fieldPointer = (TupleComponentReference) objectPointer
				.getParent();
		int result = fieldPointer.getIndex().getInt();

		return result;
	}

	// better to get more precise source...
	private State executeFree(State state, int pid, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source) {
		Expression heapPointerExpression = arguments[0];
		CIVLHeapType heapType = (CIVLHeapType) ((CIVLPointerType) heapPointerExpression
				.getExpressionType()).baseType();
		Expression pointerExpression = arguments[1];
		SymbolicExpression heapPointer = argumentValues[0];
		SymbolicExpression firstElementPointer = argumentValues[1];
		SymbolicExpression heapObjectPointer;
		Evaluation eval;
		int index;
		SymbolicExpression undef;

		eval = getAndCheckHeapObjectPointer(heapPointer, firstElementPointer,
				pointerExpression.getSource(), state);
		state = eval.state;
		heapObjectPointer = eval.value;
		index = getMallocIndex(firstElementPointer);
		undef = heapType.getMalloc(index).getUndefinedObject();
		state = primaryExecutor.assign(source, state, heapObjectPointer, undef);
		return state;
	}

	@SuppressWarnings("unused")
	private State executeMemcpy(State state, int pid, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source) {

		// TODO: implement me
		return null;
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
	 * Returns the size of a bundle.
	 * 
	 * @param state
	 * @param pid
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @param civlSource
	 * @return The size of a bundle.
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

	/*
	 * Creates a bundle from the memory region specified by ptr and size,
	 * copying the data into the new bundle:
	 * 
	 * $bundle $bundle_pack(void *ptr, int size);
	 * 
	 * Copies the data out of the bundle into the region specified:
	 * 
	 * void $bundle_unpack($bundle bundle, void *ptr, int size);
	 */

	private State executeBundlePack(State state, int pid,
			CIVLBundleType bundleType, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		Expression pointerExpr = arguments[0];
		// Expression sizeExpr = arguments[1];
		SymbolicExpression pointer = argumentValues[0];
		NumericExpression size = (NumericExpression) argumentValues[1];
		// ReferenceExpression symRef = evaluator.getSymRef(pointer);
		// ReferenceKind kind = symRef.referenceKind();
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
		// NumericExpression elementSize = evaluator.sizeof(source,
		// elementType);
		// BooleanExpression pathCondition = state.pathCondition();
		// BooleanExpression zeroSizeClaim = universe.equals(size, zero);
		// Reasoner reasoner = universe.reasoner(pathCondition);
		// ResultType zeroSizeValid = reasoner.valid(zeroSizeClaim)
		// .getResultType();
		array = getArrayFromPointer(state, pointerExpr, pointer, size, source);
		//
		// if (zeroSizeValid == ResultType.YES) {
		// array = universe.emptyArray(elementType);
		// } else {
		// BooleanExpression oneCountClaim = universe
		// .equals(size, elementSize);
		// ResultType oneCountValid = reasoner.valid(oneCountClaim)
		// .getResultType();
		//
		// if (oneCountValid == ResultType.YES) {
		// Evaluation eval = evaluator.dereference(
		// pointerExpr.getSource(), state, pointer);
		// SymbolicExpression element0 = eval.value;
		//
		// state = eval.state;
		// pathCondition = state.pathCondition();
		// array = universe.array(elementType,
		// new Singleton<SymbolicExpression>(element0));
		// } else {
		// BooleanExpression divisibility = universe.divides(elementSize,
		// size);
		// ResultType divisibilityValid = reasoner.valid(divisibility)
		// .getResultType();
		// NumericExpression count;
		//
		// if (divisibilityValid != ResultType.YES) {
		// Certainty certainty = divisibilityValid == ResultType.MAYBE ?
		// Certainty.MAYBE
		// : Certainty.PROVEABLE;
		// CIVLStateException e = new CIVLStateException(
		// ErrorKind.OTHER, certainty,
		// "sizeof element does not divide size argument",
		// state, source);
		//
		// log.report(e);
		// pathCondition = universe.and(pathCondition, divisibility);
		// state = stateFactory.setPathCondition(state, pathCondition);
		// reasoner = universe.reasoner(pathCondition);
		// }
		// count = universe.divide(size, elementSize);
		// switch (kind) {
		// case ARRAY_ELEMENT: {
		// NumericExpression startIndex = ((ArrayElementReference) symRef)
		// .getIndex();
		// SymbolicExpression arrayPointer = evaluator.parentPointer(
		// source, pointer);
		// Evaluation eval = evaluator.dereference(source, state,
		// arrayPointer);
		// SymbolicExpression originalArray = eval.value;
		// NumericExpression endIndex = universe
		// .add(startIndex, count);
		//
		// state = eval.state;
		// array = evaluator.getSubArray(originalArray, startIndex,
		// endIndex, state, source);
		// break;
		// }
		// case IDENTITY:
		// throw new CIVLStateException(ErrorKind.POINTER,
		// Certainty.MAYBE,
		// "unable to get concrete count of 0 or 1 from size",
		// state, source);
		// case NULL: { // size must be 0
		// Certainty certainty = zeroSizeValid == ResultType.MAYBE ?
		// Certainty.MAYBE
		// : Certainty.PROVEABLE;
		// CIVLStateException e = new CIVLStateException(
		// ErrorKind.POINTER, certainty,
		// "null pointer only valid with size 0", state,
		// source);
		//
		// log.report(e);
		// pathCondition = universe.and(pathCondition, zeroSizeClaim);
		// state = stateFactory.setPathCondition(state, pathCondition);
		// reasoner = universe.reasoner(pathCondition);
		// array = universe.emptyArray(elementType);
		// }
		// case OFFSET: {
		// // either size is zero or size is 1 and offset is 0
		// throw new CIVLStateException(ErrorKind.POINTER,
		// Certainty.MAYBE, "possible out of bounds pointer",
		// state, source);
		// }
		// case TUPLE_COMPONENT: {
		// throw new CIVLStateException(ErrorKind.POINTER,
		// Certainty.MAYBE,
		// "unable to get concrete count of 0 or 1 from size",
		// state, source);
		// }
		// case UNION_MEMBER:
		// throw new CIVLInternalException("dereference union member",
		// source);
		// default:
		// throw new CIVLInternalException("unreachable", source);
		// }
		// }
		// }
		bundle = universe.unionInject(symbolicBundleType, indexObj, array);
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, lhs, bundle);
		return state;
	}

	private State executeBundleUnpack(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression bundle = argumentValues[0];
		// Expression pointerExpr = arguments[1];
		// Expression sizeExpr = arguments[1];
		SymbolicExpression pointer = argumentValues[1];
		ReferenceExpression symRef = evaluator.getSymRef(pointer);
		ReferenceKind kind = symRef.referenceKind();
		// SymbolicType referencedType = evaluator.referencedType(source, state,
		// pointer);
		// IntObject index = (IntObject) bundle.argument(0);
		SymbolicExpression array = (SymbolicExpression) bundle.argument(1);
		// SymbolicType elementType = ((SymbolicArrayType) array.type())
		// .elementType();
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
								SymbolicExpression element = universe
										.arrayRead(array, universe.integer(i));

								targetArray = universe.arrayWrite(targetArray,
										targetIndex, element);
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

	private State executeCommCreate(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression comm;
		SymbolicExpression nprocs = argumentValues[0];
		NumericExpression size;
		int nprocsConcrete;
		SymbolicExpression procs;
		SymbolicExpression buff;
		SymbolicExpression buff1d;
		List<SymbolicExpression> queueComponents = new LinkedList<SymbolicExpression>();
		List<SymbolicExpression> emptyQueues = new LinkedList<SymbolicExpression>();
		List<SymbolicExpression> buff1ds = new LinkedList<SymbolicExpression>();
		List<SymbolicExpression> commComponents = new LinkedList<SymbolicExpression>();
		Model model = state.getScope(0).lexicalScope().model();
		CIVLType queueType = model.queueType();
		CIVLType messageType = model.mesageType();
		CIVLType commType = model.commType();
		SymbolicType dynamicQueueType = queueType.getDynamicType(universe);
		SymbolicType dynamicMessageType = messageType.getDynamicType(universe);
		SymbolicExpression emptyQueue; // Just need one since immutable.
		ArrayList<SymbolicExpression> procQueueArrayComponent = new ArrayList<SymbolicExpression>();
		SymbolicExpression procQueueArray = null;
		SymbolicExpression procArray = null;
		SymbolicTupleType procQueueType = null;

		assert nprocs instanceof NumericExpression;
		size = universe.multiply((NumericExpression) nprocs, evaluator.sizeof(
				arguments[1].getSource(), evaluator.modelFactory()
						.processSymbolicType()));
		procs = getArrayFromPointer(state, arguments[1], argumentValues[1],
				size, source);
		nprocsConcrete = evaluator.extractInt(source,
				(NumericExpression) nprocs);

		/* create procQueue array */
		for (int i = 0; i < nprocsConcrete; i++) {
			ArrayList<SymbolicExpression> procArrayComponent = new ArrayList<SymbolicExpression>();
			ArrayList<SymbolicExpression> procQueueComponent = new ArrayList<SymbolicExpression>();
			ArrayList<SymbolicType> procQueueTypeComponent = new ArrayList<SymbolicType>();

			procQueueComponent.add(universe.integer(1));// procs queue length
			procQueueTypeComponent.add(universe.integer(1).type());
			SymbolicExpression singleProc = universe.arrayRead(procs,
					universe.integer(i));
			procArrayComponent.add(singleProc);
			procArray = universe.array(singleProc.type(), procArrayComponent);
			procQueueComponent.add(procArray);
			procQueueTypeComponent.add(procArray.type());
			procQueueType = universe.tupleType(
					universe.stringObject("__procQueue__"),
					procQueueTypeComponent);
			procQueueArrayComponent.add(universe.tuple(procQueueType,
					procQueueComponent));
		}
		procQueueArray = universe.array(procQueueType, procQueueArrayComponent);
		// SymbolicType test = universe.pureType(procQueueArray.type());
		queueComponents.add(universe.integer(0));
		queueComponents.add(universe.emptyArray(dynamicMessageType));
		assert dynamicQueueType instanceof SymbolicTupleType;
		emptyQueue = universe.tuple((SymbolicTupleType) dynamicQueueType,
				queueComponents);
		for (int i = 0; i < nprocsConcrete; i++) {
			emptyQueues.add(emptyQueue);
		}
		buff1d = universe.array(dynamicQueueType, emptyQueues);
		for (int i = 0; i < nprocsConcrete; i++) {
			buff1ds.add(buff1d);
		}
		buff = universe.array(universe.arrayType(dynamicQueueType), buff1ds);
		commComponents.add(nprocs);
		commComponents.add(procQueueArray);
		commComponents.add(buff);
		assert commType.getDynamicType(universe) instanceof SymbolicTupleType;
		comm = universe.tuple(
				(SymbolicTupleType) commType.getDynamicType(universe),
				commComponents);
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, lhs, comm);
		return state;
	}

	private State executeCommEnqueue(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {

		// SymbolicExpression procArray;
		CIVLSource commArgSource = arguments[0].getSource();
		// int nprocs;
		int source = -1;
		int dest = -1;
		NumericExpression sourceExpression;
		NumericExpression destExpression;
		SymbolicExpression buf; // buf has type $queue[][]
		SymbolicExpression bufRow; // buf[source], has type $queue[] and
									// corresponds
		SymbolicExpression queue; // the particular $queue for this source and
									// dest
		int queueLength;
		SymbolicExpression messages;
		List<SymbolicExpression> messagesElements = new LinkedList<SymbolicExpression>();
		SymbolicExpression newMessage;
		int commScopeID = evaluator
				.getScopeId(commArgSource, argumentValues[0]);
		int commVariableID = evaluator.getVariableId(commArgSource,
				argumentValues[0]);
		SymbolicExpression comm = evaluator.dereference(commArgSource, state,
				argumentValues[0]).value;
		// int int_rank = evaluator.findRank(comm, pid);

		assert universe.tupleRead(comm, zeroObject) instanceof NumericExpression;
		// nprocs = evaluator.extractInt(commArgSource,
		// (NumericExpression) universe.tupleRead(comm, zeroObject));
		// procArray = (SymbolicExpression) universe.tupleRead(comm,
		// universe.intObject(1));
		// evaluator.dereference(commArgSource, state,
		// argumentValues[1]);
		// if (int_rank < 0) {
		// throw new CIVLExecutionException(ErrorKind.COMMUNICATION,
		// Certainty.CONCRETE,
		// "The process attempting to call $comm_enqueue is not in the communicator "
		// + arguments[0].toString() + ".", commArgSource);
		// }
		newMessage = argumentValues[1];
		source = evaluator.extractInt(arguments[1].getSource(),
				(NumericExpression) universe.tupleRead(newMessage, zeroObject));
		if (!evaluator.isProcInCommWithRank(comm, pid, source)) {
			throw new CIVLExecutionException(ErrorKind.COMMUNICATION,
					Certainty.CONCRETE,
					"The process cannot call $comm_enqueue of communicator "
							+ arguments[0].toString()
							+ " using source rank of " + source + ".",
					commArgSource);
		}
		dest = evaluator.extractInt(arguments[1].getSource(),
				(NumericExpression) universe.tupleRead(newMessage, oneObject));
		// Find the array index corresponding to the source proc and dest proc
		// for (int i = 0; i < nprocs; i++) {
		// SymbolicExpression proc = universe.arrayRead(procArray,
		// universe.integer(i));
		// int procID = evaluator.extractInt(commArgSource,
		// (NumericExpression) universe.tupleRead(proc, zeroObject));
		// if (procID == pid) {
		// source = i;
		// }
		// if (universe.tupleRead(proc, zeroObject).equals(
		// universe.tupleRead(newMessage, universe.intObject(1)))) {
		// dest = i;
		// }
		// if (dest >= 0 && source >= 0) {
		// break;
		// }
		// }
		assert source >= 0;
		assert dest >= 0;
		sourceExpression = universe.integer(source);
		destExpression = universe.integer(dest);
		buf = universe.tupleRead(comm, universe.intObject(2));
		bufRow = universe.arrayRead(buf, sourceExpression);
		queue = universe.arrayRead(bufRow, destExpression);
		messages = universe.tupleRead(queue, universe.intObject(1));
		for (int i = 0; i < evaluator.extractInt(commArgSource,
				universe.length(messages)); i++) {
			messagesElements.add(universe.arrayRead(messages,
					universe.integer(i)));
		}
		messagesElements.add(newMessage);
		messages = universe.array(
				((SymbolicArrayType) messages.type()).elementType(),
				messagesElements);
		assert universe.tupleRead(queue, zeroObject) instanceof NumericExpression;
		queueLength = evaluator.extractInt(commArgSource,
				(NumericExpression) universe.tupleRead(queue, zeroObject));
		queueLength++;
		queue = universe.tupleWrite(queue, universe.intObject(0),
				universe.integer(queueLength));
		queue = universe.tupleWrite(queue, universe.intObject(1), messages);
		bufRow = universe.arrayWrite(bufRow, destExpression, queue);
		buf = universe.arrayWrite(buf, sourceExpression, bufRow);
		comm = universe.tupleWrite(comm, universe.intObject(2), buf);
		state = stateFactory.setVariable(state, commVariableID, commScopeID,
				comm);
		return state;
	}

	private State executeCommDequeue(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression comm;
		CIVLSource commArgSource = arguments[0].getSource();
		NumericExpression sourceExpression;
		NumericExpression destExpression;
		SymbolicExpression buf; // buf has type $queue[][]
		SymbolicExpression bufRow; // buf[source], has type $queue[] and
									// corresponds
		SymbolicExpression queue; // the particular $queue for this source and
									// dest
		int queueLength;
		SymbolicExpression messages;
		SymbolicExpression message = null;
		int commScopeID = evaluator
				.getScopeId(commArgSource, argumentValues[0]);
		int commVariableID = evaluator.getVariableId(commArgSource,
				argumentValues[0]);
		int numMessages;

		comm = evaluator.dereference(commArgSource, state, argumentValues[0]).value;
		assert universe.tupleRead(comm, zeroObject) instanceof NumericExpression;
		sourceExpression = (NumericExpression) argumentValues[1];
		destExpression = (NumericExpression) argumentValues[2];
		buf = universe.tupleRead(comm, universe.intObject(2));
		bufRow = universe.arrayRead(buf, sourceExpression);
		queue = universe.arrayRead(bufRow, destExpression);
		messages = universe.tupleRead(queue, universe.intObject(1));
		numMessages = evaluator.extractInt(commArgSource,
				universe.length(messages));
		for (int i = 0; i < numMessages; i++) {
			if (universe.tupleRead(
					universe.arrayRead(messages, universe.integer(i)),
					universe.intObject(2)).equals(argumentValues[3])) {
				message = universe.arrayRead(messages, universe.integer(i));
				messages = universe.removeElementAt(messages, i);
				break;
			}
		}
		assert universe.tupleRead(queue, zeroObject) instanceof NumericExpression;
		queueLength = evaluator.extractInt(commArgSource,
				(NumericExpression) universe.tupleRead(queue, zeroObject));
		queueLength--;
		queue = universe.tupleWrite(queue, universe.intObject(0),
				universe.integer(queueLength));
		queue = universe.tupleWrite(queue, universe.intObject(1), messages);
		bufRow = universe.arrayWrite(bufRow, destExpression, queue);
		buf = universe.arrayWrite(buf, sourceExpression, bufRow);
		comm = universe.tupleWrite(comm, universe.intObject(2), buf);
		state = stateFactory.setVariable(state, commVariableID, commScopeID,
				comm);
		if (lhs != null) {
			assert message != null;
			state = primaryExecutor.assign(state, pid, lhs, message);
		}
		return state;
	}

	private State executeWork(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		CallOrSpawnStatement call;
		LHSExpression lhs;
		int numArgs;

		if (!(statement instanceof CallOrSpawnStatement)) {
			throw new CIVLInternalException("Unsupported statement for civlc",
					statement);
		}
		call = (CallOrSpawnStatement) statement;
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
		case "$free":
			state = executeFree(state, pid, arguments, argumentValues,
					statement.getSource());
			state = transition(state, state.getProcessState(pid),
					statement.target());
			break;
		case "$bundle_pack":
			state = executeBundlePack(state, pid, (CIVLBundleType) call
					.function().returnType(), lhs, arguments, argumentValues,
					statement.getSource());
			state = transition(state, state.getProcessState(pid),
					statement.target());
			break;
		case "$bundle_unpack":
			state = executeBundleUnpack(state, pid, arguments, argumentValues,
					statement.getSource());
			state = transition(state, state.getProcessState(pid),
					statement.target());
			break;
		case "$bundle_size":
			state = executeBundleSize(state, pid, lhs, arguments,
					argumentValues, statement.getSource());
			state = transition(state, state.getProcessState(pid),
					statement.target());
			break;
		case "$comm_create":
			state = executeCommCreate(state, pid, lhs, arguments,
					argumentValues, statement.getSource());
			state = transition(state, state.getProcessState(pid),
					statement.target());
			break;
		case "$comm_enqueue":
			state = executeCommEnqueue(state, pid, arguments, argumentValues);
			state = transition(state, state.getProcessState(pid),
					statement.target());
			break;
		case "$comm_dequeue":
			state = executeCommDequeue(state, pid, lhs, arguments,
					argumentValues);
			state = transition(state, state.getProcessState(pid),
					statement.target());
			break;
		// case "printf":
		// state = executePrintf(state, pid, argumentValues);
		// state = transition(state, state.getProcessState(pid),
		// statement.target());
		// break;
		case "$exit":
			state = executeExit(state, pid);
			// No transition after an exit because the process no longer exists.
			break;
		case "$comm_add":
			state = executeCommAdd(state, pid, lhs, arguments, argumentValues,
					statement.getSource());
			state = transition(state, state.getProcessState(pid),
					statement.target());
			break;
		case "$memcpy":
		case "$message_pack":
		case "$message_source":
		case "$message_tag":
		case "$message_dest":
		case "$message_size":
		case "$message_unpack":
		case "$comm_destroy":
		case "$comm_nprocs":
		case "$comm_probe":
		case "$comm_seek":
		case "$comm_chan_size":
		case "$comm_total_size":
			throw new CIVLUnimplementedFeatureException(name.name(), statement);
		default:
			throw new CIVLInternalException("Unknown civlc function: " + name,
					statement);
		}
		return state;
	}

	@Override
	public State execute(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
	}

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

	@Override
	public boolean containsFunction(String name) {
		Set<String> functions = new HashSet<String>();

		functions.add("$malloc");
		functions.add("$free");
		functions.add("$write");
		return functions.contains(name);
	}

	@Override
	public State initialize(State state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public State wrapUp(State state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression getGuard(State state, int pid, Statement statement) {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		CallOrSpawnStatement call;
		// LHSExpression lhs;
		int numArgs;
		BooleanExpression guard;

		if (!(statement instanceof CallOrSpawnStatement)) {
			throw new CIVLInternalException("Unsupported statement for civlc",
					statement);
		}
		call = (CallOrSpawnStatement) statement;
		numArgs = call.arguments().size();
		name = call.function().name();
		// lhs = call.lhs();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = null;

			arguments[i] = call.arguments().get(i);
			try {
				eval = evaluator.evaluate(state, pid, arguments[i]);
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return universe.falseExpression();
			}
			argumentValues[i] = eval.value;
			state = eval.state;
		}

		switch (name.name()) {
		case "$comm_dequeue":
			try {
				guard = getDequeueGuard(state, pid, arguments, argumentValues);
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return universe.falseExpression();
			}
			break;
		case "$comm_add":
			// try {
			// guard = getCommAddGuard(state, pid, arguments, argumentValues,
			// statement.getSource());
			// } catch (UnsatisfiablePathConditionException e) {
			// // the error that caused the unsatifiable path condition should
			// // already have been reported.
			// return universe.falseExpression();
			// }
			// break;
		case "$free":
		case "$bundle_pack":
		case "$bundle_unpack":
		case "$bundle_size":
		case "$comm_create":
		case "$comm_enqueue":
		case "printf":
		case "$exit":
		case "$memcpy":
		case "$message_pack":
		case "$message_source":
		case "$message_tag":
		case "$message_dest":
		case "$message_size":
		case "$message_unpack":
		case "$comm_destroy":
		case "$comm_nprocs":
		case "$comm_probe":
		case "$comm_seek":
		case "$comm_chan_size":
		case "$comm_total_size":
			guard = universe.trueExpression();
			break;

		default:
			throw new CIVLInternalException("Unknown civlc function: " + name,
					statement);
		}
		return guard;
	}

	private BooleanExpression getDequeueGuard(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression comm;
		CIVLSource commArgSource = arguments[0].getSource();
		NumericExpression sourceExpression;
		NumericExpression destExpression;
		SymbolicExpression buf; // buf has type $queue[][]
		SymbolicExpression bufRow; // buf[source], has type $queue[]
		SymbolicExpression queue; // particular $queue for this source and dest
		SymbolicExpression messages;
		int numMessages;
		boolean enabled = false;
		// int int_rank;
		int dest;

		comm = evaluator.dereference(commArgSource, state, argumentValues[0]).value;
		// int_rank = evaluator.findRank(comm, pid);
		// if (int_rank < 0) {
		// throw new CIVLExecutionException(ErrorKind.COMMUNICATION,
		// Certainty.CONCRETE,
		// "The process attempting to call $comm_dequeue is not in the communicator "
		// + arguments[0].toString() + ".", commArgSource);
		// }
		destExpression = (NumericExpression) argumentValues[2];
		dest = evaluator.extractInt(null, destExpression);
		if (!evaluator.isProcInCommWithRank(comm, pid, dest)) {
			throw new CIVLExecutionException(ErrorKind.COMMUNICATION,
					Certainty.CONCRETE,
					"The process cannot call $comm_dequeue of communicator "
							+ arguments[0].toString()
							+ " using destination rank of " + dest + ".",
					commArgSource);
		}

		assert universe.tupleRead(comm, zeroObject) instanceof NumericExpression;
		sourceExpression = (NumericExpression) argumentValues[1];
		buf = universe.tupleRead(comm, universe.intObject(2));
		bufRow = universe.arrayRead(buf, sourceExpression);
		queue = universe.arrayRead(bufRow, destExpression);
		messages = universe.tupleRead(queue, universe.intObject(1));
		numMessages = evaluator.extractInt(commArgSource,
				universe.length(messages));
		for (int i = 0; i < numMessages; i++) {
			if (universe.tupleRead(
					universe.arrayRead(messages, universe.integer(i)),
					universe.intObject(2)).equals(argumentValues[3])) {
				// We have a message with the right tag!
				enabled = true;
				break;
			}
		}
		return universe.bool(enabled);
	}

	/**
	 * Transition a process from one location to another. If the new location is
	 * in a different scope, create a new scope or move to the parent scope as
	 * necessary.
	 * 
	 * @param state
	 *            The old state.
	 * @param process
	 *            The process undergoing the transition.
	 * @param target
	 *            The end location of the transition.
	 * @return A new state where the process is at the target location.
	 */
	private State transition(State state, ProcessState process, Location target) {
		state = stateFactory.setLocation(state, process.getPid(), target);
		// state = stateFactory.canonic(state);
		return state;
	}

	private State executeCommAdd(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		Evaluation eval;
		SymbolicExpression procValue = argumentValues[1];
		SymbolicExpression comm;
		SymbolicExpression nprocs;
		int int_nprocs;
		SymbolicExpression procs;
		NumericExpression rank = (NumericExpression) argumentValues[2];
		SymbolicExpression procQueue;
		// assert procQueue != null;
		SymbolicExpression queueLength;
		SymbolicExpression procsArray;
		ArrayList<SymbolicExpression> newProcsArrayComponent = new ArrayList<>();
		ArrayList<SymbolicType> newProcsQueueTypeComponent = new ArrayList<>();
		ArrayList<SymbolicExpression> newProcsQueueComponent = new ArrayList<>();
		ArrayList<SymbolicExpression> newProcsComponent = new ArrayList<>();
		int int_queueLength;
		SymbolicExpression newProcsArray = null;
		int procToAdd = evaluator.modelFactory().getProcessId(
				arguments[1].getSource(), procValue);
		int commScopeID = evaluator.getScopeId(arguments[0].getSource(),
				argumentValues[0]);
		int commVariableID = evaluator.getVariableId(arguments[0].getSource(),
				argumentValues[0]);
		int pRank = evaluator.extractInt(arguments[2].getSource(), rank);

		eval = evaluator.dereference(arguments[0].getSource(), state,
				argumentValues[0]);
		comm = eval.value;
		state = eval.state;
		nprocs = this.universe.tupleRead(comm, zeroObject);
		int_nprocs = evaluator.extractInt(source, (NumericExpression) nprocs);
		procs = this.universe.tupleRead(comm, oneObject);
		// // Get the exact rank
		// int_rank = evaluator.findRank(comm, pid);
		if (!evaluator.isProcInCommWithRank(comm, pid, pRank)) {
			throw new CIVLExecutionException(ErrorKind.COMMUNICATION,
					Certainty.CONCRETE,
					"The process attempting to call $comm_add of the communicator "
							+ arguments[0].toString()
							+ " doesn't have the rank of " + pRank + ".",
					source);
		}
		if (evaluator.findRank(comm, procToAdd) >= 0) {
			throw new CIVLExecutionException(ErrorKind.COMMUNICATION,
					Certainty.CONCRETE, "The process " + procToAdd
							+ " is already in the communicator "
							+ arguments[0].toString()
							+ " and thus can't be added into it again.",
					arguments[1].getSource());
		}
		procQueue = universe.arrayRead(procs, rank);
		assert procQueue != null;
		queueLength = universe.tupleRead(procQueue, zeroObject);
		procsArray = universe.tupleRead(procQueue, oneObject);
		int_queueLength = this.evaluator.extractInt(source,
				(NumericExpression) queueLength);
		for (int i = 0; i < int_queueLength; i++) {
			newProcsArrayComponent.add(universe.arrayRead(procsArray,
					universe.integer(i)));
		}
		newProcsArrayComponent.add(procValue);
		newProcsArray = universe.array(newProcsArrayComponent.get(0).type(),
				newProcsArrayComponent);
		int_queueLength++;
		newProcsQueueTypeComponent.add(universe.integerType());
		newProcsQueueTypeComponent.add(newProcsArray.type());
		newProcsQueueComponent.add(universe.integer(int_queueLength));
		newProcsQueueComponent.add(newProcsArray);
		SymbolicTupleType newProcQueueType = universe.tupleType(
				universe.stringObject("__procQueue__"),
				newProcsQueueTypeComponent);
		procQueue = universe.tuple(newProcQueueType, newProcsQueueComponent);
		for (int i = 0; i < int_nprocs; i++) {
			if (i != evaluator.extractInt(source, rank))
				newProcsComponent.add(universe.arrayRead(procs,
						universe.integer(i)));
			else {
				newProcsComponent.add(procQueue);
			}
		}
		newProcsArray = universe.array(universe.pureType(procQueue.type()),
				newProcsComponent);
		comm = universe.tupleWrite(comm, oneObject, newProcsArray);
		state = stateFactory.setVariable(state, commVariableID, commScopeID,
				comm);
		return state;
	}

	// /**
	// We don't need the guard here. An error will be report instead.
	// * The guard of the comm_add I think should be the process must be in the
	// * communicator and the thread gonna be added into the communicator should
	// * not be in the communicator at this point.
	// *
	// * @param state
	// * @param pid
	// * @param arguments
	// * @param argumentValues
	// * @return
	// * @throws UnsatisfiablePathConditionException
	// */
	// private BooleanExpression getCommAddGuard(State state, int pid,
	// Expression arguments[], SymbolicExpression argumentValues[],
	// CIVLSource source) throws UnsatisfiablePathConditionException {
	// BooleanExpression guard = null;
	// Expression commPointerExpr = arguments[0];
	// SymbolicExpression procValue = argumentValues[1];
	// DereferenceExpression commExpr = this.evaluator.modelFactory()
	// .dereferenceExpression(source, commPointerExpr);
	// Evaluation eval = this.evaluator.evaluate(state, pid, commExpr);
	// SymbolicExpression comm = eval.value;
	// state = eval.state;
	// SymbolicExpression nprocs = this.universe.tupleRead(comm, zeroObject);
	// int int_nprocs = evaluator.extractInt(source,
	// (NumericExpression) nprocs);
	// SymbolicExpression procs = this.universe.tupleRead(comm, oneObject);
	// // TODO: get real rank
	// SymbolicExpression rank = universe.integer(pid);
	// SymbolicExpression procQueue = universe.arrayRead(procs,
	// (NumericExpression) rank);
	// SymbolicExpression threadArray = universe.tupleRead(procQueue,
	// oneObject);
	// SymbolicExpression theProcess = universe.arrayRead(threadArray,
	// universe.integer(0));
	//
	// return universe.trueExpression();
	// }
}
