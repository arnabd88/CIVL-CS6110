/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.log.ErrorLog;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ResultExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpressionExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.DynamicScope;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.state.StateFactoryIF;
import edu.udel.cis.vsl.civl.util.Singleton;
import edu.udel.cis.vsl.sarl.IF.ModelResult;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.OffsetReference;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.expr.UnionMemberReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.number.real.RealNumberFactory;

/**
 * An evaluator is used to evaluate expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class Evaluator {

	// Fields..............................................................

	private ModelFactory modelFactory;

	private StateFactoryIF stateFactory;

	private SymbolicUniverse universe;

	private RealNumberFactory numberFactory = new RealNumberFactory();

	/**
	 * The process type is a tuple with one component which has integer type. It
	 * simply wraps a process ID number.
	 */
	private SymbolicTupleType processType;

	/**
	 * Map from symbolic type to a canonic symbolic expression of that type.
	 */
	private Map<SymbolicType, SymbolicExpression> typeExpressionMap = new HashMap<SymbolicType, SymbolicExpression>();

	/**
	 * The scope type is a tuple with one component which has integer type. It
	 * simply wraps a scope ID number.
	 */
	// private SymbolicTupleType scopeType;

	/**
	 * The pointer value is a triple <s,v,r> where s identifies the dynamic
	 * scope, v identifies the variable within that scope, and r identifies a
	 * point within that variable. The type of s is scopeType, which is just a
	 * tuple wrapping a single integer which is the dynamic scope ID number. The
	 * type of v is integer; it is the (static) variable ID number for the
	 * variable in its scope. The type of r is ReferenceExpression from SARL.
	 */
	private SymbolicTupleType pointerType;

	private SymbolicTupleType dynamicType;

	private SymbolicExpression nullExpression;

	private SymbolicExpression nullPointer;

	private ErrorLog log;

	private IntObject zeroObj;

	private IntObject oneObj;

	private IntObject twoObj;

	private NumericExpression zero;

	private NumericExpression one;

	private NumericExpression zeroR;

	private ReferenceExpression identityReference;

	/**
	 * An uninterpreted function used to evaluate "sizeof" on a type. It takes
	 * as input one expression of type dynamicType and returns an integer
	 * expression.
	 */
	private SymbolicExpression sizeofFunction;

	private Map<SymbolicType, NumericExpression> sizeofDynamicMap = new HashMap<SymbolicType, NumericExpression>();

	/**
	 * Reasoner with trivial context "true". Used to determine satisfiability of
	 * path conditions.
	 */
	private Reasoner trueReasoner;

	// private BooleanExpression falseExpr;

	// Constructors........................................................

	/**
	 * An evaluator is used to evaluate expressions.
	 * 
	 * @param symbolicUniverse
	 *            The symbolic universe for the expressions.
	 */
	public Evaluator(ModelFactory modelFactory, StateFactoryIF stateFactory,
			ErrorLog log) {
		SymbolicType dynamicToIntType;

		this.modelFactory = modelFactory;
		this.stateFactory = stateFactory;
		this.universe = stateFactory.symbolicUniverse();
		processType = modelFactory.processSymbolicType();
		// scopeType = modelFactory.scopeSymbolicType();
		dynamicType = modelFactory.dynamicSymbolicType();
		pointerType = modelFactory.pointerSymbolicType();
		this.log = log;
		zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		oneObj = (IntObject) universe.canonic(universe.intObject(1));
		twoObj = (IntObject) universe.canonic(universe.intObject(2));
		identityReference = (ReferenceExpression) universe.canonic(universe
				.identityReference());
		zero = (NumericExpression) universe.canonic(universe.integer(0));
		zeroR = (NumericExpression) universe.canonic(universe.zeroReal());
		one = (NumericExpression) universe.canonic(universe.integer(1));
		nullPointer = universe.canonic(makePointer(-1, -1,
				universe.nullReference()));
		nullExpression = universe.nullExpression();
		dynamicToIntType = universe.functionType(new Singleton<SymbolicType>(
				dynamicType), universe.integerType());
		sizeofFunction = universe.symbolicConstant(
				universe.stringObject("SIZEOF"), dynamicToIntType);
		sizeofFunction = universe.canonic(sizeofFunction);
		trueReasoner = universe.reasoner(universe.trueExpression());
		// falseExpr = universe.falseExpression();
	}

	// Helper methods......................................................

	/**
	 * Report a (possible) error detected in the course of evaluating an
	 * expression.
	 * 
	 * Protocol for checking conditions and reporting and recovering from
	 * errors. First, check some condition holds and call the result of that
	 * check "condsat", which may be YES, NO, or MAYBE. If condsat is YES,
	 * proceed. Otherwise, there is a problem: call this method.
	 * 
	 * This method first checks the satisfiability of the path condition, call
	 * the result "pcsat". Logs a violation with certainty determined as
	 * follows:
	 * <ul>
	 * <li>pcsat=YES && condsat=NO : certainty=PROVEABLE</li>
	 * <li>pcsat=YES && condsat=MAYBE : certainty=MAYBE</li>
	 * <li>pcsat=MAYBE && condsat=NO : certainty=MAYBE</li>
	 * <li>pcsat=MAYBE && condsat=MAYBE : certainty=MAYBE</li>
	 * <li>pcsat=NO: no error to report</li>
	 * </ul>
	 * 
	 * Returns the state obtained by adding the claim to the pc of the given
	 * state.
	 * 
	 */
	private State logError(CIVLSource source, State state,
			BooleanExpression claim, ResultType resultType,
			ErrorKind errorKind, String message)
			throws UnsatisfiablePathConditionException {
		BooleanExpression pc = state.pathCondition(), newPc;
		BooleanExpression npc = universe.not(pc);
		ValidityResult validityResult = trueReasoner.validOrModel(npc);
		ResultType nsat = validityResult.getResultType();
		Certainty certainty;
		CIVLStateException error;

		// performance! need to cache the satisfiability of each pc somewhere
		// negation is slow
		// maybe add "nsat" to Reasoner.
		if (nsat == ResultType.YES)
			// no error to report---an infeasible path
			throw new UnsatisfiablePathConditionException();
		if (nsat == ResultType.MAYBE)
			certainty = Certainty.MAYBE;
		else { // pc is definitely satisfiable
			if (resultType == ResultType.NO) {
				// need something satisfying PC and not claim...
				ValidityResult claimResult = trueReasoner.validOrModel(universe
						.or(npc, claim));

				if (claimResult.getResultType() == ResultType.NO) {
					ModelResult modelResult = (ModelResult) claimResult;

					certainty = Certainty.CONCRETE;
					message += "\nCounterexample:\n" + modelResult.getModel()
							+ "\n";
				} else {
					certainty = Certainty.PROVEABLE;
				}
			} else {
				certainty = Certainty.MAYBE;
			}
		}
		error = new CIVLStateException(errorKind, certainty, message, state,
				source);
		log.report(error);
		newPc = universe.and(pc, claim);
		// need to check satisfiability again because failure to do so
		// could lead to a SARLException when some subsequent evaluation
		// takes place
		nsat = trueReasoner.valid(universe.not(newPc)).getResultType();
		if (nsat == ResultType.YES)
			throw new UnsatisfiablePathConditionException();
		state = stateFactory.setPathCondition(state, newPc);
		return state;
	}

	private NumericExpression zeroOf(CIVLSource source, CIVLType type) {
		if (type instanceof CIVLPrimitiveType) {
			if (((CIVLPrimitiveType) type).primitiveTypeKind() == PrimitiveTypeKind.INT)
				return zero;
			if (((CIVLPrimitiveType) type).primitiveTypeKind() == PrimitiveTypeKind.REAL)
				return zeroR;
		}
		throw new CIVLInternalException("Expected integer or real type, not "
				+ type, source);
	}

	// private Certainty certaintyOf(CIVLSource source, ResultType resultType) {
	// if (resultType == ResultType.NO)
	// return Certainty.PROVEABLE;
	// if (resultType == ResultType.MAYBE)
	// return Certainty.MAYBE;
	// throw new CIVLInternalException(
	// "This method should only be called with result type of NO or MAYBE",
	// source);
	// }

	/**
	 * Gets a Java conrete int from a symbolic expression or throws exception.
	 * 
	 * @param expression
	 *            a numeric expression expected to hold concrete int value
	 * @return the concrete int
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	public int extractInt(CIVLSource source, NumericExpression expression) {
		IntegerNumber result = (IntegerNumber) universe
				.extractNumber(expression);

		if (result == null)
			throw new CIVLInternalException(
					"Unable to extract concrete int from " + expression, source);
		return result.intValue();
	}

	/**
	 * Gets a concrete Java int from the field of a symbolic expression of tuple
	 * type or throws exception.
	 * 
	 * @param tuple
	 *            symbolic expression of tuple type
	 * @param fieldIndex
	 *            index of a field in that tuple
	 * @return the concrete int value of that field
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	private int extractIntField(CIVLSource source, SymbolicExpression tuple,
			IntObject fieldIndex) {
		NumericExpression field = (NumericExpression) universe.tupleRead(tuple,
				fieldIndex);

		return extractInt(source, field);
	}

	/**
	 * Given an array, a start index, and end index, returns the array which is
	 * the subsequence of the given array consisting of the elements in
	 * positions start index through end index minus one. The length of the new
	 * array is endIndex - startIndex.
	 * 
	 * @param array
	 * @param startIndex
	 * @param endIndex
	 * @param assumption
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public SymbolicExpression getSubArray(SymbolicExpression array,
			NumericExpression startIndex, NumericExpression endIndex,
			State state, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		// if startIndex is zero and endIndex is length, return array
		// verify startIndex >=0 and endIndex<= Length
		// if startIndex==endIndex return emptyArray
		// else if startIndex and endIndex are concrete, create concrete array
		// else need array lambdas or subsequence operation: todo
		BooleanExpression pathCondition = state.pathCondition();
		Reasoner reasoner = universe.reasoner(pathCondition);
		NumericExpression length = universe.length(array);
		SymbolicArrayType arrayType = (SymbolicArrayType) array.type();
		SymbolicType elementType = arrayType.elementType();

		if (reasoner.isValid(universe.equals(zero, startIndex))
				&& reasoner.isValid(universe.equals(length, endIndex)))
			return array;
		else {
			BooleanExpression claim = universe.lessThanEquals(zero, startIndex);
			ResultType valid = reasoner.valid(claim).getResultType();

			if (valid != ResultType.YES) {
				state = logError(source, state, claim, valid,
						ErrorKind.OUT_OF_BOUNDS, "negative start index");
				pathCondition = state.pathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(endIndex, length);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = logError(source, state, claim, valid,
						ErrorKind.OUT_OF_BOUNDS,
						"end index exceeds length of array");
				pathCondition = state.pathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(startIndex, endIndex);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = logError(source, state, claim, valid,
						ErrorKind.OUT_OF_BOUNDS,
						"start index greater than end index");
				pathCondition = state.pathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			if (reasoner.isValid(universe.equals(startIndex, endIndex))) {
				return universe.emptyArray(elementType);
			} else {
				IntegerNumber concreteStart = (IntegerNumber) reasoner
						.extractNumber(startIndex);
				IntegerNumber concreteEnd = (IntegerNumber) reasoner
						.extractNumber(endIndex);

				if (concreteStart != null && concreteEnd != null) {
					int startInt = concreteStart.intValue();
					int endInt = concreteEnd.intValue();
					LinkedList<SymbolicExpression> valueList = new LinkedList<SymbolicExpression>();

					for (int i = startInt; i < endInt; i++)
						valueList.add(universe.arrayRead(array,
								universe.integer(i)));
					return universe.array(elementType, valueList);
				}
			}
		}
		throw new CIVLInternalException("Unable to extract sub-array", source);
	}

	/**
	 * Makes a pointer value from the given dynamic scope ID, variable ID, and
	 * symbolic reference value.
	 * 
	 * @param scopeId
	 *            ID number of a dynamic scope
	 * @param varId
	 *            ID number of a variable within that scope
	 * @param symRef
	 *            a symbolic reference to a point within the variable
	 * @return a pointer value as specified by the 3 componentss
	 */
	private SymbolicExpression makePointer(int scopeId, int varId,
			ReferenceExpression symRef) {
		SymbolicExpression scopeField = modelFactory.scopeValue(scopeId);
		SymbolicExpression varField = universe.integer(varId);
		SymbolicExpression result = universe.tuple(
				pointerType,
				Arrays.asList(new SymbolicExpression[] { scopeField, varField,
						symRef }));

		return result;
	}

	/**
	 * Tells whether the given symbolic expression is a pointer value.
	 * 
	 * @param pointer
	 *            any symbolic expression
	 * @return true iff the expression is a pointer value
	 */
	private boolean isPointer(SymbolicExpression pointer) {
		return pointer.type() == pointerType;
	}

	/**
	 * Returns the pointer value obtained by replacing the symRef component of
	 * the given pointer value with the given symRef.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @param symRef
	 *            a symbolic refererence expression
	 * @return the pointer obtained by modifying the given one by replacing its
	 *         symRef field with the given symRef
	 */
	public SymbolicExpression setSymRef(SymbolicExpression pointer,
			ReferenceExpression symRef) {
		return universe.tupleWrite(pointer, twoObj, symRef);
	}

	/**
	 * Given a non-trivial pointer, i.e., a pointer to some location inside an
	 * object, returns the parent pointer. For example, a pointer to an array
	 * element returns the pointer to the array.
	 * 
	 * @param pointer
	 *            non-trivial pointer
	 * @return pointer to parent
	 * @throws CIVLInternalException
	 *             if pointer is trivial
	 */
	public SymbolicExpression parentPointer(CIVLSource source,
			SymbolicExpression pointer) {
		ReferenceExpression symRef = getSymRef(pointer);

		if (symRef instanceof NTReferenceExpression)
			return setSymRef(pointer,
					((NTReferenceExpression) symRef).getParent());
		throw new CIVLInternalException("Expected non-trivial pointer: "
				+ pointer, source);
	}

	/**
	 * Returns the parent pointer of the given pointer, or null if the given
	 * pointer is a variable pointer (i.e., has no parent pointer).
	 * 
	 * @param pointer
	 *            any pointer value
	 * @return parent pointer or null
	 */
	public SymbolicExpression getParentPointer(SymbolicExpression pointer) {
		ReferenceExpression symRef = getSymRef(pointer);

		if (symRef instanceof NTReferenceExpression)
			return setSymRef(pointer,
					((NTReferenceExpression) symRef).getParent());
		return null;
	}

	/**
	 * Given an expression of pointer type, evaluates that expression in the
	 * given state to get a pointer value, and then dereferences that to yield
	 * the value pointed to.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pid
	 *            PID of the process in which this evaluation occurs
	 * @param operand
	 *            an expression of pointer type
	 * @return the referenced value
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation dereference(State state, int pid, Expression operand)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, operand);

		return dereference(operand.getSource(), eval.state, eval.value);
	}

	/**
	 * Evaluates pointer addition. Pointer addition involves the addition of a
	 * pointer expression and an integer.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process evaluating the pointer addition
	 * @param expression
	 *            the pointer addition expression
	 * @param pointer
	 *            the result of evaluating argument 0 of expression
	 * @param offset
	 *            the result of evaluating argument 1 of expression
	 * @return the result of evaluating the sum of the pointer and the integer
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation pointerAdd(State state, int pid,
			BinaryExpression expression, SymbolicExpression pointer,
			NumericExpression offset)
			throws UnsatisfiablePathConditionException {
		ReferenceExpression symRef = getSymRef(pointer);

		if (symRef.isArrayElementReference()) {
			SymbolicExpression arrayPointer = parentPointer(
					expression.getSource(), pointer);
			Evaluation eval = dereference(expression.getSource(), state,
					arrayPointer);
			// eval.value is now a symbolic expression of array type.
			SymbolicArrayType arrayType = (SymbolicArrayType) eval.value.type();
			ArrayElementReference arrayElementRef = (ArrayElementReference) symRef;
			NumericExpression oldIndex = arrayElementRef.getIndex();
			NumericExpression newIndex = universe.add(oldIndex, offset);

			if (arrayType.isComplete()) { // check bounds
				NumericExpression length = universe.length(eval.value);
				BooleanExpression claim = universe.and(
						universe.lessThanEquals(zero, newIndex),
						universe.lessThanEquals(newIndex, length));
				BooleanExpression assumption = eval.state.pathCondition();
				ResultType resultType = universe.reasoner(assumption)
						.valid(claim).getResultType();

				if (resultType != ResultType.YES) {
					eval.state = logError(expression.getSource(), eval.state,
							claim, resultType, ErrorKind.OUT_OF_BOUNDS,
							"Pointer addition resulted in out of bounds array index:\nindex = "
									+ newIndex + "\nlength = " + length);
				}
			}
			eval.value = setSymRef(pointer, universe.arrayElementReference(
					arrayElementRef.getParent(), newIndex));
			return eval;
		} else if (symRef.isOffsetReference()) {
			OffsetReference offsetRef = (OffsetReference) symRef;
			NumericExpression oldOffset = offsetRef.getOffset();
			NumericExpression newOffset = universe.add(oldOffset, offset);
			BooleanExpression claim = universe.and(
					universe.lessThanEquals(zero, newOffset),
					universe.lessThanEquals(newOffset, one));
			BooleanExpression assumption = state.pathCondition();
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();
			Evaluation eval;

			if (resultType != ResultType.YES) {
				state = logError(expression.getSource(), state, claim,
						resultType, ErrorKind.OUT_OF_BOUNDS,
						"Pointer addition resulted in out of bounds object pointer:\noffset = "
								+ newOffset);
			}
			eval = new Evaluation(state, setSymRef(pointer,
					universe.offsetReference(offsetRef.getParent(), newOffset)));
			return eval;
		} else
			throw new CIVLUnimplementedFeatureException(
					"Pointer addition for anything other than array elements or variables",
					expression);
	}

	/**
	 * Evaluates pointer subtraction.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process performing this evaluation
	 * @param expression
	 *            the pointer subtraction expression
	 * @param p1
	 *            the result of evaluating argument 0 of expression; should be a
	 *            pointer
	 * @param p2
	 *            the result of evaluating argument 1 of expression; should be a
	 *            pointer
	 * @return the integer symbolic expression resulting from subtracting the
	 *         two pointers together with the post-state if side-effects
	 *         occurred
	 */
	private Evaluation pointerSubtract(State state, int pid,
			BinaryExpression expression, SymbolicExpression p1,
			SymbolicExpression p2) {
		throw new CIVLUnimplementedFeatureException("pointer subtraction",
				expression);
	}

	/**
	 * Evaluates an address-of expression "&e".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process performing the evaluation
	 * @param expression
	 *            the address-of expression
	 * @return the symbolic expression of pointer type resulting from evaluating
	 *         the address of the argument
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateAddressOf(State state, int pid,
			AddressOfExpression expression)
			throws UnsatisfiablePathConditionException {
		return reference(state, pid, expression.operand());
	}

	/**
	 * Evaluates a dereference expression "*e".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process performing the evaluation
	 * @param expression
	 *            the dereference expression
	 * @return the symbolic expression value that result from dereferencing the
	 *         pointer value argument
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateDereference(State state, int pid,
			DereferenceExpression expression)
			throws UnsatisfiablePathConditionException {
		return dereference(state, pid, expression.pointer());
	}

	/**
	 * <p>
	 * General method for evaluating "short-circuited" conditional expressions
	 * that may involve logged side-effects on the path condition. These include
	 * expressions of the form <code>c?t:f</code>, <code>p&&q</code>, and
	 * <code>p||q</code>. The latter two are a special case of the first:
	 * <ul>
	 * <li><code>p&&q</code> is equivalent to <code>p?q:false</code></li>
	 * <li><code>p||q</code> is equivalent to <code>p?true:q</code></li>
	 * </ul>
	 * </p>
	 * 
	 * <p>
	 * Say the path condition is <code>p</code> and the expression is
	 * <code>(c?t:f)</code>.
	 * </p>
	 * 
	 * <p>
	 * If <code>c</code> is valid (assuming <code>p</code>), the result is just
	 * the result of evaluating <code>t</code>. If <code>!c</code> is valid, the
	 * result is just the result of evaluating <code>f</code>. The subtle case
	 * is where neither of those is valid, in which case, proceed as follows:
	 * </p>
	 * 
	 * <p>
	 * When evaluating <code>t</code>, assume <code>c</code> holds. When
	 * evaluating <code>f</code>, assume <code>!c</code> holds. Say
	 * <code>eval(p&&c, t)</code> results in <code>(p1,v1)</code> and
	 * <code>eval(p&&!c,f)</code> results in <code>(p2,v2)</code>. Then return
	 * <code>(p1||p2, (c?v1:v2))</code>.
	 * </p>
	 * 
	 * <p>
	 * Example: <code>x==0 ? 1/w + y/(1-x) : 1/z + y/x</code>, <code>p</code>=
	 * <code>true</code>. <code>eval(p&&c, t)</code> yields
	 * <code>(x==0 && w!=0, 1/w+y/(1-x))</code> together with a logged warning
	 * that <code>w!=0</code> has been assumed. <code>eval(p&&!c,f)</code>
	 * yields <code>(x!=0 && z!=0, 1/z+y/x)</code> together with a logged
	 * warning that <code>z!=0</code> has been assumed. The resulting path
	 * condition is <code>(x==0 && w!=0) || (x!=0 && z!=0)</code>.
	 * </p>
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of process evaluating this expression
	 * @param condition
	 *            the boolean conditional expression <code>c</code>
	 * @param trueBranch
	 *            the sub-expression which becomes the value if <code>c</code>
	 *            evaluates to <code>true</code>
	 * @param falseBranch
	 *            the sub-expression which becomes the value if <code>c</code>
	 *            evaluates to <code>false</code>
	 * @return the evaluation with the properly updated state and the
	 *         conditional value
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateConditional(State state, int pid,
			Expression condition, Expression trueBranch, Expression falseBranch)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, condition);
		BooleanExpression c = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.pathCondition();
		Reasoner reasoner = universe.reasoner(assumption);

		if (reasoner.isValid(c))
			return evaluate(eval.state, pid, trueBranch);
		if (reasoner.isValid(universe.not(c)))
			return evaluate(eval.state, pid, falseBranch);
		else {
			State s1 = stateFactory.setPathCondition(eval.state,
					universe.and(assumption, c));
			State s2 = stateFactory.setPathCondition(eval.state,
					universe.and(assumption, universe.not(c)));
			Evaluation eval1 = evaluate(s1, pid, trueBranch);
			Evaluation eval2 = evaluate(s2, pid, falseBranch);

			eval.state = stateFactory.setPathCondition(
					eval.state,
					universe.or(eval1.state.pathCondition(),
							eval2.state.pathCondition()));
			eval.value = universe.cond(c, eval1.value, eval2.value);
			return eval;
		}
	}

	/**
	 * Evaluates a conditional expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            the pid of the currently executing process.
	 * @param expression
	 *            The conditional expression.
	 * @return A symbolic expression for the result of the conditional.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateCond(State state, int pid,
			ConditionalExpression expression)
			throws UnsatisfiablePathConditionException {
		return evaluateConditional(state, pid, expression.getCondition(),
				expression.getTrueBranch(), expression.getFalseBranch());
	}

	/**
	 * Evaluates a short-circuit "and" expression "p&&q".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process evaluating this expression
	 * @param expression
	 *            the and expression
	 * @return the result of applying the AND operator to the two arguments
	 *         together with the post-state whose path condition may contain the
	 *         side-effects resulting from evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateAnd(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		BooleanExpression p = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.pathCondition();
		Reasoner reasoner = universe.reasoner(assumption);

		if (reasoner.isValid(p))
			return evaluate(eval.state, pid, expression.right());
		if (reasoner.isValid(universe.not(p))) {
			eval.value = universe.falseExpression();
			return eval;
		} else {
			BooleanExpression assumptionAndp = universe.and(assumption, p);
			State s1 = stateFactory
					.setPathCondition(eval.state, assumptionAndp);
			Evaluation eval1 = evaluate(s1, pid, expression.right());
			BooleanExpression pcTemp = eval1.state.pathCondition();

			if (!assumptionAndp.equals(pcTemp)) {
				BooleanExpression pc = universe.or(pcTemp,
						universe.and(assumption, universe.not(p)));

				eval.state = stateFactory.setPathCondition(eval.state, pc);
			}
			// Reason for above: In the common case where there
			// are no side effects, this would set the path condition to
			// (assumption && p) || (assumption && !p),
			// which does not get simplified to just "assumption",
			// as one would like. So it is handled as a special case:
			// check whether pcTemp equals assumption && p
			// (i.e., the evaluation of expression.right() did not
			// add any side-effects). If this holds, then pc is just
			// assumption.
			eval.value = universe.and(p, (BooleanExpression) eval1.value);
			return eval;
		}
	}

	/**
	 * Evaluates a short-circuit "or" expression "p||q".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process evaluating this expression
	 * @param expression
	 *            the OR expression
	 * @return the result of applying the OR operator to the two arguments
	 *         together with the post-state whose path condition may contain the
	 *         side-effects resulting from evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateOr(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		BooleanExpression p = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.pathCondition();
		Reasoner reasoner = universe.reasoner(assumption);

		// TODO: handle special common case as in evaluateAnd.
		// Look at evaluation of ternary operator too?

		if (reasoner.isValid(p)) {
			eval.value = universe.trueExpression();
			return eval;
		}
		if (reasoner.isValid(universe.not(p))) {
			return evaluate(eval.state, pid, expression.right());
		} else {
			State s1 = stateFactory.setPathCondition(eval.state,
					universe.and(assumption, universe.not(p)));
			Evaluation eval1 = evaluate(s1, pid, expression.right());
			BooleanExpression pc = universe.or(eval1.state.pathCondition(),
					universe.and(assumption, p));

			eval.state = stateFactory.setPathCondition(eval.state, pc);
			eval.value = universe.or(p, (BooleanExpression) eval1.value);
			return eval;
		}
	}

	/**
	 * Evaluate a "dot" expression used to navigate to a field in a record,
	 * "e.f".
	 * 
	 * @param state
	 *            The state of the model
	 * @param pid
	 *            The pid of the process evaluating this expression
	 * @param expression
	 *            The dot expression
	 * @return The symbolic expression resulting from evaluating the expression
	 *         together with the post-state which may incorporate side-effects
	 *         resulting from the evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateDot(State state, int pid,
			DotExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.struct());
		SymbolicExpression structValue = eval.value;
		int fieldIndex = expression.fieldIndex();

		eval.value = universe.tupleRead(structValue,
				universe.intObject(fieldIndex));
		return eval;
	}

	/**
	 * Evaluate a subscript expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The array index expression.
	 * @return A symbolic expression for an array read.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateSubscript(State state, int pid,
			SubscriptExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.array());
		SymbolicExpression array = eval.value;
		SymbolicArrayType arrayType = (SymbolicArrayType) array.type();
		NumericExpression index;

		eval = evaluate(state, pid, expression.index());
		index = (NumericExpression) eval.value;
		if (arrayType.isComplete()) {
			NumericExpression length = universe.length(array);
			BooleanExpression assumption = eval.state.pathCondition();
			BooleanExpression claim = universe.and(
					universe.lessThanEquals(zero, index),
					universe.lessThan(index, length));
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES) {
				eval.state = logError(expression.getSource(), eval.state,
						claim, resultType, ErrorKind.OUT_OF_BOUNDS,
						"Out of bounds array index:\nindex = " + index
								+ "\nlength = " + length);
			}
		}
		eval.value = universe.arrayRead(array, index);
		return eval;
	}

	/**
	 * Evaluate a binary expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The binary expression.
	 * @return A symbolic expression for the binary operation.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBinary(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		BINARY_OPERATOR operator = expression.operator();

		if (operator == BINARY_OPERATOR.AND)
			return evaluateAnd(state, pid, expression);
		if (operator == BINARY_OPERATOR.OR)
			return evaluateOr(state, pid, expression);
		else {
			Evaluation eval = evaluate(state, pid, expression.left());
			SymbolicExpression left = eval.value;
			SymbolicExpression right;

			eval = evaluate(state, pid, expression.right());
			right = eval.value;
			switch (expression.operator()) {
			case PLUS:
				eval.value = universe.add((NumericExpression) left,
						(NumericExpression) right);
				break;
			case MINUS:
				eval.value = universe.subtract((NumericExpression) left,
						(NumericExpression) right);
				break;
			case TIMES:
				eval.value = universe.multiply((NumericExpression) left,
						(NumericExpression) right);
				break;
			case DIVIDE: {
				BooleanExpression assumption = eval.state.pathCondition();
				NumericExpression denominator = (NumericExpression) right;
				BooleanExpression claim = universe.neq(
						zeroOf(expression.getSource(),
								expression.getExpressionType()), denominator);
				ResultType resultType = universe.reasoner(assumption)
						.valid(claim).getResultType();

				if (resultType != ResultType.YES) {
					eval.state = logError(expression.getSource(), eval.state,
							claim, resultType, ErrorKind.DIVISION_BY_ZERO,
							"Division by zero");
				}
				eval.value = universe.divide((NumericExpression) left,
						denominator);
				break;
			}
			case LESS_THAN:
				eval.value = universe.lessThan((NumericExpression) left,
						(NumericExpression) right);
				break;
			case LESS_THAN_EQUAL:
				eval.value = universe.lessThanEquals((NumericExpression) left,
						(NumericExpression) right);
				break;
			case EQUAL:
				eval.value = universe.equals(left, right);
				break;
			case NOT_EQUAL:
				eval.value = universe.neq(left, right);
				break;
			case MODULO: {
				BooleanExpression assumption = eval.state.pathCondition();
				NumericExpression denominator = (NumericExpression) right;
				BooleanExpression claim = universe.neq(
						zeroOf(expression.getSource(),
								expression.getExpressionType()), denominator);
				ResultType resultType = universe.reasoner(assumption)
						.valid(claim).getResultType();

				if (resultType != ResultType.YES) {
					eval.state = this.logError(expression.getSource(),
							eval.state, claim, resultType,
							ErrorKind.DIVISION_BY_ZERO,
							"Modulus denominator is zero");
				}
				eval.value = universe.modulo((NumericExpression) left,
						denominator);
				break;
			}
			case POINTER_ADD:
				eval = pointerAdd(state, pid, expression, left,
						(NumericExpression) right);
				break;
			case POINTER_SUBTRACT:
				eval = pointerSubtract(state, pid, expression, left, right);
				break;
			case AND:
			case OR:
				throw new CIVLInternalException("unreachable", expression);
			default:
				throw new CIVLUnimplementedFeatureException("Operator "
						+ expression.operator(), expression);
			}
			return eval;
		}
	}

	/**
	 * Evaluate a boolean literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The boolean literal expression.
	 * @return The symbolic representation of the boolean literal expression.
	 */
	private Evaluation evaluateBooleanLiteral(State state, int pid,
			BooleanLiteralExpression expression) {
		return new Evaluation(state, universe.bool(expression.value()));
	}

	/**
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The cast expression.
	 * @return The symbolic representation of the cast expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateCast(State state, int pid,
			CastExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression arg = expression.getExpression();
		CIVLType argType = arg.getExpressionType();
		Evaluation eval = evaluate(state, pid, arg);
		SymbolicExpression value = eval.value;
		CIVLType castType = expression.getCastType();
		TypeEvaluation typeEval = getDynamicType(eval.state, pid, castType,
				expression.getSource(), false);
		SymbolicType endType = typeEval.type;

		state = typeEval.state;
		if (argType.isIntegerType() && castType.isPointerType()) {
			// only good cast is from 0 to null pointer
			BooleanExpression assumption = state.pathCondition();
			BooleanExpression claim = universe.equals(zero, value);
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES) {
				state = logError(expression.getSource(), state, claim,
						resultType, ErrorKind.INVALID_CAST,
						"Cast from non-zero integer to pointer");
				eval.state = state;
			}
			eval.value = nullPointer;
			return eval;
		} else if (argType.isPointerType() && castType.isPointerType()) {
			// pointer to pointer: for now...no change.
			return eval;
		}
		try {
			eval.value = universe.cast(endType, eval.value);
		} catch (SARLException e) {
			CIVLStateException error = new CIVLStateException(
					ErrorKind.INVALID_CAST, Certainty.NONE,
					"SARL could not cast: " + e, eval.state,
					expression.getSource());

			log.report(error);
			throw new UnsatisfiablePathConditionException();
		}
		return eval;
	}

	public NumericExpression sizeof(CIVLSource source, SymbolicType type) {
		NumericExpression result = sizeofDynamicMap.get(type);

		if (result == null) {

			if (type.isBoolean())
				result = modelFactory.booleanType().getSizeof();
			else if (type == modelFactory.dynamicSymbolicType())
				result = modelFactory.dynamicType().getSizeof();
			else if (type.isInteger())
				result = modelFactory.integerType().getSizeof();
			else if (type == modelFactory.processSymbolicType())
				result = modelFactory.processType().getSizeof();
			else if (type.isReal())
				result = modelFactory.realType().getSizeof();
			else if (type == modelFactory.scopeSymbolicType())
				result = modelFactory.scopeType().getSizeof();
			else if (type instanceof SymbolicCompleteArrayType) {
				SymbolicCompleteArrayType arrayType = (SymbolicCompleteArrayType) type;

				result = sizeof(source, arrayType.elementType());
				result = universe.multiply(arrayType.extent(),
						(NumericExpression) result);
			} else if (type instanceof SymbolicArrayType) {
				throw new CIVLInternalException(
						"sizeof applied to incomplete array type", source);
			} else {
				// wrap the type in an expression of type dynamicTYpe
				SymbolicExpression typeExpr = expressionOfType(type);

				result = (NumericExpression) universe.apply(sizeofFunction,
						new Singleton<SymbolicExpression>(typeExpr));
			}
			sizeofDynamicMap.put(type, result);
		}
		return result;
	}

	public Evaluation evaluateSizeofType(CIVLSource source, State state,
			int pid, CIVLType type) throws UnsatisfiablePathConditionException {
		Evaluation eval;

		if (type instanceof CIVLPrimitiveType) {
			NumericExpression value = ((CIVLPrimitiveType) type).getSizeof();
			BooleanExpression facts = ((CIVLPrimitiveType) type).getFacts();
			BooleanExpression pathCondition = universe.and(facts,
					state.pathCondition());

			state = stateFactory.setPathCondition(state, pathCondition);
			eval = new Evaluation(state, value);
		} else if (type instanceof CIVLCompleteArrayType) {
			NumericExpression extentValue;

			eval = evaluate(state, pid, ((CIVLCompleteArrayType) type).extent());
			extentValue = (NumericExpression) eval.value;
			eval = evaluateSizeofType(source, eval.state, pid,
					((CIVLArrayType) type).elementType());
			eval.value = universe.multiply(extentValue,
					(NumericExpression) eval.value);
		} else if (type instanceof CIVLArrayType) {
			throw new CIVLInternalException(
					"sizeof applied to incomplete array type", source);
		} else {
			NumericExpression sizeof;
			BooleanExpression pathCondition;

			eval = dynamicTypeOf(state, pid, type, source, false);
			sizeof = (NumericExpression) universe.apply(sizeofFunction,
					new Singleton<SymbolicExpression>(eval.value));
			pathCondition = universe.and(eval.state.pathCondition(),
					universe.lessThan(zero, sizeof));
			eval.value = sizeof;
			eval.state = stateFactory.setPathCondition(state, pathCondition);
		}
		return eval;
	}

	private Evaluation evaluateSizeofTypeExpression(State state, int pid,
			SizeofTypeExpression expression)
			throws UnsatisfiablePathConditionException {
		return evaluateSizeofType(expression.getSource(), state, pid,
				expression.getTypeArgument());
	}

	private Evaluation evaluateSizeofExpressionExpression(State state, int pid,
			SizeofExpressionExpression expression)
			throws UnsatisfiablePathConditionException {
		return evaluateSizeofType(expression.getSource(), state, pid,
				expression.getArgument().getExpressionType());
	}

	/**
	 * Evalute an integer literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The integer literal expression.
	 * @return The symbolic representation of the integer literal expression.
	 */
	private Evaluation evaluateIntegerLiteral(State state, int pid,
			IntegerLiteralExpression expression) {
		return new Evaluation(state, universe.integer(expression.value()
				.intValue()));
	}

	private Evaluation evaluateSelf(State state, int pid,
			SelfExpression expression) {
		return new Evaluation(state, modelFactory.processValue(pid));
	}

	/**
	 * Evaluate a real literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The real literal expression.
	 * @return The symbolic representation of the real literal expression.
	 */
	private Evaluation evaluateRealLiteral(State state, int pid,
			RealLiteralExpression expression) {
		return new Evaluation(state, universe.number(universe
				.numberObject(numberFactory.rational(expression.value()
						.toPlainString()))));
	}

	/**
	 * Evaluate a string literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The string literal expression.
	 * @return The symbolic representation of the string literal expression.
	 */
	private Evaluation evaluateStringLiteral(State state, int pid,
			StringLiteralExpression expression) {
		return new Evaluation(state, universe.stringExpression(expression
				.value()));
	}

	/**
	 * Evaluate a unary expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The unary expression.
	 * @return The symbolic representation of the unary expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateUnary(State state, int pid,
			UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.operand());

		switch (expression.operator()) {
		case NEGATIVE:
			eval.value = universe.minus((NumericExpression) eval.value);
			break;
		case NOT:
			eval.value = universe.not((BooleanExpression) eval.value);
			break;
		default:
			throw new CIVLInternalException("Unknown unary operator "
					+ expression.operator(), expression);
		}
		return eval;
	}

	/**
	 * Evaluate a variable expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The variable expression.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateVariable(State state, int pid,
			VariableExpression expression)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression value = state.valueOf(pid, expression.variable());

		if (value == null || value.isNull()) {
			CIVLExecutionException e = new CIVLStateException(
					ErrorKind.UNDEFINED_VALUE, Certainty.PROVEABLE,
					"Attempt to read uninitialized variable", state,
					expression.getSource());

			log.report(e);
			throw new UnsatisfiablePathConditionException();
		}
		return new Evaluation(state, value);
	}

	private Evaluation evaluateResult(State state, int pid,
			ResultExpression expression) {
		// TODO
		// this is used in a contract post-condition as a variable to
		// refer to the result returned by a function. $result.
		// get rid of ResultExpression and instead create a variable
		// in the outermost scope of any function with non-void
		// return type, store the result of return in that variable.
		// Add method in Function to get that variable. (and set it?)
		// Model builder will translate $result to that variable.
		throw new CIVLUnimplementedFeatureException(
				"$result not yet implemented: " + expression.getSource());
	}

	private TypeEvaluation getDynamicType(State state, int pid, CIVLType type,
			CIVLSource source, boolean isDefinition)
			throws UnsatisfiablePathConditionException {
		TypeEvaluation result;

		// if type has a state variable and computeStructs is false, use
		// variable else compute
		if (type instanceof CIVLPrimitiveType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLPointerType) {
			result = new TypeEvaluation(state, pointerType);
		} else if (type.getStateVariable() != null && !isDefinition) {
			SymbolicExpression value = state.valueOf(pid,
					type.getStateVariable());

			result = new TypeEvaluation(state, getType(source, value));
		} else if (type instanceof CIVLArrayType) {
			CIVLArrayType arrayType = (CIVLArrayType) type;
			TypeEvaluation elementTypeEval = getDynamicType(state, pid,
					arrayType.elementType(), source, false);

			if (arrayType.isComplete()) {
				Evaluation lengthEval = evaluate(elementTypeEval.state, pid,
						((CIVLCompleteArrayType) arrayType).extent());
				NumericExpression length = (NumericExpression) lengthEval.value;

				result = new TypeEvaluation(lengthEval.state,
						universe.arrayType(elementTypeEval.type, length));
			} else {
				result = new TypeEvaluation(elementTypeEval.state,
						universe.arrayType(elementTypeEval.type));
			}
		} else if (type instanceof CIVLStructType) {
			CIVLStructType structType = (CIVLStructType) type;
			int numFields = structType.numFields();
			LinkedList<SymbolicType> componentTypes = new LinkedList<SymbolicType>();

			for (int i = 0; i < numFields; i++) {
				StructField field = structType.getField(i);
				TypeEvaluation componentEval = getDynamicType(state, pid,
						field.type(), source, false);

				state = componentEval.state;
				componentTypes.add(componentEval.type);
			}
			result = new TypeEvaluation(state, universe.tupleType(structType
					.name().stringObject(), componentTypes));
		} else if (type instanceof CIVLBundleType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else
			throw new CIVLInternalException("Unreachable", source);
		return result;
	}

	private SymbolicExpression computeInitialValue(State s, Variable variable,
			SymbolicType dynamicType, int dyscopeId) {
		CIVLType type = variable.type();
		int vid = variable.vid();
		SymbolicExpression result;

		if (!variable.isInput()
				&& (type instanceof CIVLPrimitiveType || type instanceof CIVLPointerType)) {
			result = nullExpression;
		} else {
			StringObject name = universe.stringObject("X_s" + dyscopeId + "v"
					+ vid);

			result = universe.symbolicConstant(name, dynamicType);
		}
		return result;
	}

	private Evaluation dynamicTypeOf(State state, int pid, CIVLType type,
			CIVLSource source, boolean isDefinition)
			throws UnsatisfiablePathConditionException {
		TypeEvaluation typeEval = getDynamicType(state, pid, type, source,
				isDefinition);
		SymbolicExpression expr = expressionOfType(typeEval.type);
		Evaluation result = new Evaluation(typeEval.state, expr);

		return result;
	}

	private Evaluation evaluateDynamicTypeOf(State state, int pid,
			DynamicTypeOfExpression expression)
			throws UnsatisfiablePathConditionException {
		return dynamicTypeOf(state, pid, expression.getType(),
				expression.getSource(), true);
	}

	private Evaluation evaluateInitialValue(State state, int pid,
			InitialValueExpression expression)
			throws UnsatisfiablePathConditionException {
		Variable variable = expression.variable();
		CIVLType type = variable.type();
		Evaluation result;

		if (type.isHeapType()) {
			result = new Evaluation(state,
					((CIVLHeapType) type).getInitialValue());
		} else {
			TypeEvaluation typeEval = getDynamicType(state, pid, type,
					expression.getSource(), false);
			int sid = state.getScopeId(pid, variable);
			SymbolicExpression value = computeInitialValue(typeEval.state,
					variable, typeEval.type, sid);

			result = new Evaluation(typeEval.state, value);
		}
		return result;
	}

	// Exported methods...

	public ModelFactory modelFactory() {
		return modelFactory;
	}

	public StateFactoryIF stateFactory() {
		return stateFactory;
	}

	public SymbolicUniverse universe() {
		return universe;
	}

	/**
	 * Returns the log used by this evaluator to record an property violations
	 * encountered.
	 * 
	 * @return the error log
	 */
	public ErrorLog log() {
		return log;
	}

	/**
	 * Returns the pointer type: the type of the symbolic expressions used to
	 * represent pointer values.
	 * 
	 * @return the pointer type
	 */
	public SymbolicType pointerType() {
		return pointerType;
	}

	public SymbolicExpression nullPointer() {
		return nullPointer;
	}

	/**
	 * Tells whether the given symbolic expression is the null pointer value.
	 * 
	 * @param pointer
	 *            any symbolic expression
	 * @return true iff the expression is the null pointer value
	 */
	public boolean isNullPointer(SymbolicExpression pointer) {
		return isPointer(pointer) && getSymRef(pointer).isNullReference();
	}

	/**
	 * Returns the process type: the type of the symbolic expressions used as
	 * values assigned to variables of type <code>$proc</code>.
	 * 
	 * @return the process type
	 */
	public SymbolicType processType() {
		return processType;
	}

	/**
	 * Given a pointer value, returns the dynamic scope ID component of that
	 * pointer value.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return the dynamic scope ID component of that pointer value
	 */
	public int getScopeId(CIVLSource source, SymbolicExpression pointer) {
		return modelFactory.getScopeId(source,
				universe.tupleRead(pointer, zeroObj));
	}

	/**
	 * Given a pointer value, returns the variable ID component of that value.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return the variable ID component of that value
	 */
	public int getVariableId(CIVLSource source, SymbolicExpression pointer) {
		return extractIntField(source, pointer, oneObj);
	}

	/**
	 * Given a pointer value, returns the symbolic reference component of that
	 * value. The "symRef" refers to a sub-structure of the variable pointed to.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return the symRef component
	 */
	public ReferenceExpression getSymRef(SymbolicExpression pointer) {
		SymbolicExpression result = universe.tupleRead(pointer, twoObj);

		if (!(result instanceof ReferenceExpression))
			throw new RuntimeException("Expected ReferenceExpression, not: "
					+ result.toStringBufferLong());
		return (ReferenceExpression) result;
	}

	/**
	 * Creates a pointer value by evaluating a left-hand-side expression in the
	 * given state.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pid
	 *            the process ID of the process in which this evaluation is
	 *            taking place
	 * @param operand
	 *            the left hand side expression we are taking the address of
	 * @return the pointer value
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation reference(State state, int pid, LHSExpression operand)
			throws UnsatisfiablePathConditionException {
		Evaluation result;

		if (operand instanceof VariableExpression) {
			Variable variable = ((VariableExpression) operand).variable();
			int sid = state.getScopeId(pid, variable);
			int vid = variable.vid();

			result = new Evaluation(state, makePointer(sid, vid,
					identityReference));
		} else if (operand instanceof SubscriptExpression) {
			Evaluation refEval = reference(state, pid,
					((SubscriptExpression) operand).array());
			SymbolicExpression arrayPointer = refEval.value;
			ReferenceExpression oldSymRef = getSymRef(arrayPointer);
			NumericExpression index;
			ReferenceExpression newSymRef;

			result = evaluate(refEval.state, pid,
					((SubscriptExpression) operand).index());
			index = (NumericExpression) result.value;
			newSymRef = universe.arrayElementReference(oldSymRef, index);
			result.value = setSymRef(arrayPointer, newSymRef);
		} else if (operand instanceof DereferenceExpression) {
			result = evaluate(state, pid,
					((DereferenceExpression) operand).pointer());
		} else if (operand instanceof DotExpression) {
			Evaluation eval = reference(state, pid,
					(LHSExpression) ((DotExpression) operand).struct());
			SymbolicExpression structPointer = eval.value;
			ReferenceExpression oldSymRef = getSymRef(structPointer);
			int index = ((DotExpression) operand).fieldIndex();
			ReferenceExpression newSymRef = universe.tupleComponentReference(
					oldSymRef, universe.intObject(index));

			eval.value = setSymRef(structPointer, newSymRef);
			result = eval;
		} else
			throw new CIVLInternalException("Unknown kind of LHSExpression",
					operand);
		return result;
	}

	/**
	 * Given a pointer value, dereferences it in the given state to yield the
	 * symbolic expression value stored at the referenced location.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pointer
	 *            a pointer value which refers to some sub-structure in the
	 *            state
	 * @return the value pointed to
	 */
	public Evaluation dereference(CIVLSource source, State state,
			SymbolicExpression pointer) {
		// how to figure out if pointer is null pointer?
		try {
			int sid = getScopeId(source, pointer);
			int vid = getVariableId(source, pointer);
			ReferenceExpression symRef = getSymRef(pointer);
			SymbolicExpression variableValue = state.getScope(sid)
					.getValue(vid);
			Evaluation result = new Evaluation(state, universe.dereference(
					variableValue, symRef));

			return result;
			// TODO: this should be an internal exception, it is more
			// expected if a reference has not been defined:
		} catch (CIVLInternalException e) {
			throw new CIVLStateException(ErrorKind.POINTER, Certainty.MAYBE,
					"Undefined pointer value?", state, source);
		}
	}

	private String symRefToString(ReferenceExpression symRef, CIVLSource source) {
		switch (symRef.referenceKind()) {
		case ARRAY_ELEMENT: {
			// parent[i]
			ArrayElementReference aref = (ArrayElementReference) symRef;

			return symRefToString(aref.getParent(), source) + "["
					+ aref.getIndex() + "]";
		}
		case IDENTITY: // empty string
			return "";
		case NULL: // NULL
			return "NULL";
		case OFFSET: {// parent+i
			OffsetReference oref = (OffsetReference) symRef;

			return symRefToString(oref.getParent(), source) + "+"
					+ oref.getOffset();
		}
		case TUPLE_COMPONENT: {// .i
			TupleComponentReference tref = (TupleComponentReference) symRef;

			return symRefToString(tref.getParent(), source) + "."
					+ tref.getIndex();
		}
		case UNION_MEMBER: {// #i
			UnionMemberReference uref = (UnionMemberReference) symRef;

			return symRefToString(uref.getParent(), source) + "#"
					+ uref.getIndex();
		}
		default:
			throw new CIVLInternalException("unreachable", source);
		}
	}

	/**
	 * Provide a nice-human readable representation of the pointer.
	 * 
	 * @param pointer
	 */
	public String pointerToString(CIVLSource source, State state,
			SymbolicExpression pointer) {
		String result = "";

		try {
			int sid = getScopeId(source, pointer);
			int vid = getVariableId(source, pointer);
			ReferenceExpression symRef = getSymRef(pointer);
			DynamicScope dyscope = state.getScope(sid);
			Scope scope = dyscope.lexicalScope();
			Variable variable = scope.getVariable(vid);
			String variableName = variable.name().name();

			result = "Ptr[scope=" + sid + ", &" + variableName;
			result += symRefToString(symRef, source);
			result += "]";

		} catch (CIVLInternalException e) {
			result += "ERROR";
		}
		return result;
	}

	/**
	 * Returns the dynamic type pointed to by a pointer. Can be used even if the
	 * pointer can't be dereferenced (because it points off the end of an
	 * object, for example).
	 * 
	 * @param source
	 * @param state
	 * @param pointer
	 * @return
	 */
	public SymbolicType referencedType(CIVLSource source, State state,
			SymbolicExpression pointer) {
		int sid = getScopeId(source, pointer);
		int vid = getVariableId(source, pointer);
		ReferenceExpression symRef = getSymRef(pointer);
		SymbolicExpression variableValue = state.getScope(sid).getValue(vid);
		SymbolicType variableType = variableValue.type();
		SymbolicType result = universe.referencedType(variableType, symRef);

		return result;
	}

	/**
	 * Given a symbolic type, returns a canonic symbolic expression which
	 * somehow wraps that type so it can be used as a value. Nothing should be
	 * assumed about the symbolic expression. To extract the type from such an
	 * expression, use method {@link #getType}.
	 * 
	 * @param type
	 *            a symbolic type
	 * @return a canonic symbolic expression wrapping that type
	 */
	public SymbolicExpression expressionOfType(SymbolicType type) {
		SymbolicExpression result;

		type = (SymbolicType) universe.canonic(type);
		result = typeExpressionMap.get(type);
		if (result == null) {
			SymbolicExpression id = universe.integer(type.id());

			result = universe.canonic(universe.tuple(dynamicType,
					new Singleton<SymbolicExpression>(id)));
			typeExpressionMap.put(type, result);
		}
		return result;
	}

	/**
	 * Given a symbolic expression returned by the method
	 * {@link #expressionOfType}, this extracts the type that was used to create
	 * that expression. If the given expression is not an expression that was
	 * created by {@link #expressionOfType}, the behavior is undefined.
	 * 
	 * @param expr
	 *            a symbolic expression returned by method
	 *            {@link #expressionOfType}
	 * @return the symbolic type used to create that expression
	 */
	public SymbolicType getType(CIVLSource source, SymbolicExpression expr) {
		int id = extractIntField(source, expr, zeroObj);

		return (SymbolicType) universe.objectWithId(id);
	}

	private String uniqueIdentifier(CIVLSource source,
			ReferenceExpression symRef) {
		String result;

		switch (symRef.referenceKind()) {
		case ARRAY_ELEMENT: {
			ArrayElementReference arrayElementRef = (ArrayElementReference) symRef;
			NumericExpression index = arrayElementRef.getIndex();
			int indexInt = extractInt(source, index);

			result = uniqueIdentifier(source, arrayElementRef.getParent());
			result += "i" + indexInt;
			break;
		}
		case IDENTITY:
			result = "";
			break;
		case NULL:
			result = "NULL";
			break;
		case OFFSET: {
			OffsetReference offsetRef = (OffsetReference) symRef;
			NumericExpression index = offsetRef.getOffset();
			int indexInt = extractInt(source, index);

			result = uniqueIdentifier(source, offsetRef.getParent());
			result += "i" + indexInt;
			break;
		}
		case TUPLE_COMPONENT: {
			TupleComponentReference tupleComponentRef = (TupleComponentReference) symRef;
			IntObject index = tupleComponentRef.getIndex();

			result = uniqueIdentifier(source, tupleComponentRef.getParent());
			result += "f" + index;
			break;
		}
		case UNION_MEMBER: {
			UnionMemberReference unionMemberRef = (UnionMemberReference) symRef;
			IntObject index = unionMemberRef.getIndex();

			result = uniqueIdentifier(source, unionMemberRef.getParent());
			result += "e" + index;
			break;
		}
		default:
			throw new CIVLInternalException("unreachable", source);
		}
		return result;
	}

	/**
	 * Returns a string that will uniquely identify (within the state) the
	 * memory location referenced by the pointer. Only applies to pointers in
	 * which all array element indexes are concrete.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return a string based on that value
	 */
	public String uniqueIdentifier(CIVLSource source, SymbolicExpression pointer) {
		int sid = getScopeId(source, pointer);
		int vid = getVariableId(source, pointer);
		ReferenceExpression symRef = getSymRef(pointer);
		String result = "_s" + sid + "v" + vid
				+ uniqueIdentifier(source, symRef);

		return result;
	}

	/**
	 * Evaluates the expression and returns the result, which is a symbolic
	 * expression value.
	 * 
	 * @param state
	 *            the state in which the evaluation takes place
	 * @param pid
	 *            the PID of the process which is evaluating the expression
	 * @param expression
	 *            the (static) expression being evaluated
	 * @return the result of the evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		ExpressionKind kind = expression.expressionKind();
		Evaluation result;

		switch (kind) {
		case ADDRESS_OF:
			result = evaluateAddressOf(state, pid,
					(AddressOfExpression) expression);
			break;
		case BINARY:
			result = evaluateBinary(state, pid, (BinaryExpression) expression);
			break;
		case BOOLEAN_LITERAL:
			result = evaluateBooleanLiteral(state, pid,
					(BooleanLiteralExpression) expression);
			break;
		case CAST:
			result = evaluateCast(state, pid, (CastExpression) expression);
			break;
		case COND:
			result = evaluateCond(state, pid,
					(ConditionalExpression) expression);
			break;
		case DEREFERENCE:
			result = evaluateDereference(state, pid,
					(DereferenceExpression) expression);
			break;
		case DOT:
			result = evaluateDot(state, pid, (DotExpression) expression);
			break;
		case DYNAMIC_TYPE_OF:
			result = evaluateDynamicTypeOf(state, pid,
					(DynamicTypeOfExpression) expression);
			break;
		case INITIAL_VALUE:
			result = evaluateInitialValue(state, pid,
					(InitialValueExpression) expression);
			break;
		case INTEGER_LITERAL:
			result = evaluateIntegerLiteral(state, pid,
					(IntegerLiteralExpression) expression);
			break;
		case REAL_LITERAL:
			result = evaluateRealLiteral(state, pid,
					(RealLiteralExpression) expression);
			break;
		case RESULT:
			result = evaluateResult(state, pid, (ResultExpression) expression);
			break;
		case SELF:
			result = evaluateSelf(state, pid, (SelfExpression) expression);
			break;
		case SIZEOF_TYPE:
			result = evaluateSizeofTypeExpression(state, pid,
					(SizeofTypeExpression) expression);
			break;
		case SIZEOF_EXPRESSION:
			result = evaluateSizeofExpressionExpression(state, pid,
					(SizeofExpressionExpression) expression);
			break;
		case STRING_LITERAL:
			result = evaluateStringLiteral(state, pid,
					(StringLiteralExpression) expression);
			break;
		case SUBSCRIPT:
			result = evaluateSubscript(state, pid,
					(SubscriptExpression) expression);
			break;
		case UNARY:
			result = evaluateUnary(state, pid, (UnaryExpression) expression);
			break;
		case VARIABLE:
			result = evaluateVariable(state, pid,
					(VariableExpression) expression);
			break;
		default:
			throw new CIVLInternalException("Unknown kind of expression: "
					+ kind, expression.getSource());
		}
		// make canonic?
		return result;
	}

}
