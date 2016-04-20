package edu.udel.cis.vsl.civl.dynamic.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableDynamicScope;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Singleton;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression.ReferenceKind;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.expr.UnionMemberReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

public class CommonSymbolicUtility implements SymbolicUtility {

	private SymbolicUniverse universe;

	private ModelFactory modelFactory;

	private IntObject zeroObj;

	private IntObject oneObj;

	private IntObject twoObj;

	private NumericExpression zero;

	private NumericExpression one;

	private CIVLErrorLogger errorLogger;

	private SymbolicExpression sizeofFunction;

	private SymbolicTupleType dynamicType;

	/**
	 * The pointer value is a triple <s,v,r> where s identifies the dynamic
	 * scope, v identifies the variable within that scope, and r identifies a
	 * point within that variable. The type of s is scopeType, which is just a
	 * tuple wrapping a single integer which is the dynamic scope ID number. The
	 * type of v is integer; it is the (static) variable ID number for the
	 * variable in its scope. The type of r is ReferenceExpression from SARL.
	 */
	private SymbolicTupleType pointerType;

	/**
	 * Map from symbolic type to a canonic symbolic expression of that type.
	 */
	private Map<SymbolicType, SymbolicExpression> typeExpressionMap = new HashMap<>();

	/**
	 * TODO ???
	 */
	private Map<SymbolicType, NumericExpression> sizeofDynamicMap = new HashMap<>();

	private CIVLHeapType heapType;

	private SymbolicTupleType procType;

	private SymbolicTupleType scopeType;

	private SymbolicTupleType functionPointerType;

	private BooleanExpression falseValue;
	private BooleanExpression trueValue;

	/**
	 * The symbolic expression of NULL pointer.
	 */
	private SymbolicExpression nullPointer;

	public CommonSymbolicUtility(SymbolicUniverse universe,
			ModelFactory modelFactory, CIVLErrorLogger errLogger) {
		SymbolicType dynamicToIntType;

		this.universe = universe;
		this.modelFactory = modelFactory;
		this.errorLogger = errLogger;
		pointerType = modelFactory.pointerSymbolicType();
		dynamicType = modelFactory.dynamicSymbolicType();
		dynamicToIntType = universe.functionType(new Singleton<SymbolicType>(
				dynamicType), universe.integerType());
		sizeofFunction = universe.symbolicConstant(
				universe.stringObject("SIZEOF"), dynamicToIntType);
		sizeofFunction = universe.canonic(sizeofFunction);
		this.zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		this.oneObj = (IntObject) universe.canonic(universe.intObject(1));
		this.twoObj = (IntObject) universe.canonic(universe.intObject(2));
		zero = (NumericExpression) universe.canonic(universe.integer(0));
		one = (NumericExpression) universe.canonic(universe.integer(1));
		this.heapType = modelFactory.heapType();
		this.procType = this.modelFactory.processSymbolicType();
		this.scopeType = this.modelFactory.scopeSymbolicType();
		this.functionPointerType = modelFactory.functionPointerSymbolicType();
		this.falseValue = (BooleanExpression) universe.canonic(universe
				.falseExpression());
		this.trueValue = (BooleanExpression) universe.canonic(universe
				.trueExpression());
		this.nullPointer = universe.canonic(this.makePointer(-1, -1,
				universe.nullReference()));
	}

	@Override
	public SymbolicExpression nullPointer() {
		return this.nullPointer;
	}

	@Override
	public int extractInt(CIVLSource source, NumericExpression expression) {
		IntegerNumber result = (IntegerNumber) universe
				.extractNumber(expression);

		// TODO make expression
		if (result == null)
			throw new CIVLInternalException(
					"Unable to extract concrete int from " + expression, source);
		return result.intValue();
	}

	@Override
	public int getDyscopeId(CIVLSource source, SymbolicExpression pointer) {
		return modelFactory.getScopeId(source,
				universe.tupleRead(pointer, zeroObj));
	}

	@Override
	public SymbolicExpression parentPointer(CIVLSource source,
			SymbolicExpression pointer) {
		ReferenceExpression symRef = getSymRef(pointer);

		if (symRef instanceof NTReferenceExpression)
			return setSymRef(pointer,
					((NTReferenceExpression) symRef).getParent());
		throw new CIVLInternalException("Expected non-trivial pointer: "
				+ pointer, source);
	}

	@Override
	public ReferenceExpression getSymRef(SymbolicExpression pointer) {
		SymbolicExpression result = universe.tupleRead(pointer, twoObj);

		assert result instanceof ReferenceExpression;
		return (ReferenceExpression) result;
	}

	@Override
	public SymbolicExpression setSymRef(SymbolicExpression pointer,
			ReferenceExpression symRef) {
		return universe.tupleWrite(pointer, twoObj, symRef);
	}

	@Override
	public int getVariableId(CIVLSource source, SymbolicExpression pointer) {
		return extractIntField(source, pointer, oneObj);
	}

	@Override
	public int extractIntField(CIVLSource source, SymbolicExpression tuple,
			IntObject fieldIndex) {
		NumericExpression field = (NumericExpression) universe.tupleRead(tuple,
				fieldIndex);

		return this.extractInt(source, field);
	}

	@Override
	public SymbolicExpression getSubArray(SymbolicExpression array,
			NumericExpression startIndex, NumericExpression endIndex,
			State state, String process, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		// if startIndex is zero and endIndex is length, return array
		// verify startIndex >=0 and endIndex<= Length
		// if startIndex==endIndex return emptyArray
		// else if startIndex and endIndex are concrete, create concrete array
		// else need array lambdas or subsequence operation: todo
		BooleanExpression pathCondition = state.getPathCondition();
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
				state = errorLogger.logError(source, state, process,
						this.stateToString(state), claim, valid,
						ErrorKind.OUT_OF_BOUNDS, "negative start index");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(endIndex, length);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = errorLogger.logError(source, state, process,
						this.stateToString(state), claim, valid,
						ErrorKind.OUT_OF_BOUNDS,
						"end index exceeds length of array");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(startIndex, endIndex);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = errorLogger.logError(source, state, process,
						this.stateToString(state), claim, valid,
						ErrorKind.OUT_OF_BOUNDS,
						"start index greater than end index");
				pathCondition = state.getPathCondition();
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
				} else {
					NumericExpression subLength = universe.subtract(endIndex,
							startIndex);
					SymbolicCompleteArrayType subArrayType = universe
							.arrayType(elementType, subLength);
					NumericSymbolicConstant index = (NumericSymbolicConstant) universe
							.symbolicConstant(universe.stringObject("i"),
									universe.integerType());
					SymbolicExpression subArrayFunction = universe.lambda(
							index,
							universe.arrayRead(array,
									universe.add(startIndex, index)));

					return universe.arrayLambda(subArrayType, subArrayFunction);

				}
			}
		}
	}

	@Override
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

	@Override
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

	@Override
	public SymbolicExpression sizeofFunction() {
		return this.sizeofFunction;
	}

	@Override
	public SymbolicExpression initialHeapValue() {
		return modelFactory.heapType().getInitialValue();
	}

	@Override
	public boolean isEmptyHeap(SymbolicExpression heapValue) {
		if (heapValue.isNull())
			return true;
		else {
			SymbolicSequence<?> heapFields = (SymbolicSequence<?>) heapValue
					.argument(0);
			int count = heapFields.size();

			for (int i = 0; i < count; i++) {
				SymbolicExpression heapField = heapFields.get(i);
				SymbolicSequence<?> heapFieldObjets = (SymbolicSequence<?>) heapField
						.argument(0);
				int size = heapFieldObjets.size();

				for (int j = 0; j < size; j++) {
					SymbolicExpression heapFieldObj = heapFieldObjets.get(j);
					SymbolicObject heapFieldObjValue = heapFieldObj.argument(0);

					if (heapFieldObjValue.symbolicObjectKind() == SymbolicObjectKind.STRING) {
						String value = ((StringObject) heapFieldObjValue)
								.getString();

						if (value.equals("UNDEFINED"))
							continue;
					}
					return false;
				}
			}
		}
		return true;
	}

	@Override
	public boolean isUndefinedConstant(SymbolicExpression value) {
		if (!value.isNull()) {
			SymbolicObject valueObj = value.argument(0);

			if (valueObj.symbolicObjectKind() == SymbolicObjectKind.EXPRESSION) {
				value = (SymbolicExpression) valueObj;
				if (value.operator() == SymbolicOperator.SYMBOLIC_CONSTANT) {
					valueObj = value.argument(0);

					if (valueObj.symbolicObjectKind() == SymbolicObjectKind.STRING) {
						String valueStr = ((StringObject) valueObj).getString();

						return valueStr.equals("UNDEFINED");
					}
				}
			}
		}
		return false;
	}

	@Override
	public SymbolicExpression makePointer(int scopeId, int varId,
			ReferenceExpression symRef) {
		SymbolicExpression scopeField = modelFactory.scopeValue(scopeId);
		SymbolicExpression varField = universe.integer(varId);
		SymbolicExpression result = universe.tuple(
				pointerType,
				Arrays.asList(new SymbolicExpression[] { scopeField, varField,
						symRef }));

		return result;
	}

	public String symbolicExpressionToString(CIVLSource source, State state,
			SymbolicExpression symbolicExpression) {
		return this.symbolicExpressionToString(source, state,
				symbolicExpression, false);
	}

	/**
	 * Obtains the string representation of a symbolic expression which is a
	 * pointer.
	 * 
	 * @param source
	 *            The source code element of the symbolic expression
	 * @param state
	 *            The state that the given symbolic expression belongs to
	 * @param pointer
	 *            The symbolic expression that is to be evaluated
	 * @return the string representation of a symbolic expression which is a
	 *         pointer
	 */
	private String functionPointerValueToString(CIVLSource source, State state,
			SymbolicExpression pointer) {
		if (pointer.operator() == SymbolicOperator.NULL)
			return pointer.toString();
		else if (pointer.operator() != SymbolicOperator.CONCRETE)
			return pointer.toString();
		else {
			int dyscopeId = getDyscopeId(source, pointer);
			if (dyscopeId < 0)
				return "UNDEFINED";
			else {
				DynamicScope dyScope = state.getScope(dyscopeId);
				SymbolicExpression funcNameExpression = universe.tupleRead(
						pointer, oneObj);
				StringBuffer funcName = this.charArrayToString(source,
						(SymbolicSequence<?>) funcNameExpression.argument(0),
						0, true);
				StringBuffer result = new StringBuffer();

				result.append('&');
				result.append("<");
				result.append("scope ");
				result.append(dyScope.lexicalScope().id());
				result.append(">(function)");
				result.append(funcName);
				return result.toString();
			}
		}
	}

	/**
	 * <p>
	 * Obtains the string representation of a symbolic expression, making
	 * pointers represented in a user-friendly way.
	 * </p>
	 * If a pointer is pointing to
	 * <ul>
	 * <li>
	 * 
	 * <pre>
	 * a variable: & variable &lt;dyscope name>;
	 * e.g., int a = 9; int * p = &a;
	 * then the representation of p would be &a&lt;d0> assuming that the name of the dynamic scope of a is d0.
	 * </pre>
	 * 
	 * </li>
	 * <li>
	 * 
	 * <pre>
	 * an element of an array: &array<dyscope name>[index];
	 * e.g., int a[5]; int *p = &a[1];
	 * then the representation of p would be &a&lt;d0>[1] assuming that the name of the dynamic scope of a is d0.
	 * </pre>
	 * 
	 * </li>
	 * <li>
	 * 
	 * <pre>
	 * a field of a struct: &struct&lt;dyscope name>.field;
	 * e.g., typedef struct {int x; int y;} A; A s; int*p = &s.y;
	 * then the representation of p would be &a&lt;d0>.y assuming that the name of the dynamic scope of a is d0.
	 * </pre>
	 * 
	 * </li>
	 * <li>
	 * 
	 * <pre>
	 * a heap cell: heapObject&lt;dyscope name, malloc ID, number of malloc call>.
	 * </pre>
	 * 
	 * </li>
	 * </ul>
	 * 
	 * @param source
	 *            The source code element of the symbolic expression.
	 * @param state
	 *            The state where the given symbolic expression is evaluated
	 *            from.
	 * @param symbolicExpression
	 *            The symbolic expression whose string representation is to be
	 *            obtained.
	 * @param atomize
	 *            True iff this is an atomic symbolic expression.
	 * @return The string representation of the given symbolic expression
	 * @throws UnsatisfiablePathConditionException
	 */
	private String symbolicExpressionToString(CIVLSource source, State state,
			SymbolicExpression symbolicExpression, boolean atomize) {
		StringBuffer result = new StringBuffer();
		SymbolicType type = symbolicExpression.type();
		SymbolicType charType = modelFactory.charType()
				.getDynamicType(universe);

		if (type == null)
			return "NULL";
		else if (type.equals(this.pointerType)) {
			return pointerValueToString(source, state, symbolicExpression);
		} else if (type.equals(this.functionPointerType)) {
			return functionPointerValueToString(source, state,
					symbolicExpression);
		} else if (symbolicExpression.operator() == SymbolicOperator.CONCRETE
				&& type instanceof SymbolicArrayType
				&& ((SymbolicArrayType) type).elementType().equals(charType)) {
			result.append("\"");
			result.append(this.charArrayToString(source,
					(SymbolicSequence<?>) symbolicExpression.argument(0), 0,
					true));
			result.append("\"");
			return result.toString();
		} else if (type.equals(procType)) {
			if (symbolicExpression.operator() != SymbolicOperator.CONCRETE)
				return symbolicExpression.toString();
			else {
				int pid = modelFactory.getProcessId(source, symbolicExpression);

				if (!modelFactory.isPocessIdDefined(pid)) {
					return "UNDEFINED";
				}
				if (pid < 0)
					return "$proc_null";
				else {
					ProcessState procState = state.getProcessState(pid);

					if (procState == null)
						return "UNDEFINED";
					return procState.name();
				}
			}
		} else if (type.equals(scopeType)) {
			int scopeId = modelFactory.getScopeId(source, symbolicExpression);

			if (!modelFactory.isScopeIdDefined(scopeId))
				return "UNDEFINED";
			if (scopeId < 0)
				return "$scope_null";
			else
				return state.getScope(scopeId).name();
		} else {
			SymbolicOperator operator = symbolicExpression.operator();
			SymbolicObject[] arguments = symbolicExpression.arguments();

			switch (operator) {
			case ADD:
				processFlexibleBinary(source, state, symbolicExpression,
						result, "+", false, atomize);
				return result.toString();
			case AND:
				processFlexibleBinary(source, state, symbolicExpression,
						result, " && ", true, atomize);
				return result.toString();
			case APPLY: {
				result.append(arguments[0].toStringBuffer(true));
				result.append("(");
				accumulate(source, state, result, ",",
						(SymbolicCollection<?>) arguments[1], false);
				result.append(")");
				return result.toString();
			}
			case ARRAY_LAMBDA:
				return symbolicExpression.toStringBufferLong().toString();
			case ARRAY_READ:
				result.append(arguments[0].toStringBuffer(true));
				result.append("[");
				result.append(arguments[1].toStringBuffer(false));
				result.append("]");
				return result.toString();
			case ARRAY_WRITE:
				result.append(arguments[0].toStringBuffer(true));
				result.append("[");
				result.append(arguments[1].toStringBuffer(false));
				result.append(":=");
				result.append(arguments[2].toStringBuffer(false));
				result.append("]");
				return result.toString();
			case CAST:
				result.append('(');
				result.append(type.toStringBuffer(false));
				result.append(')');
				result.append(arguments[0].toStringBuffer(true));
				return result.toString();
			case CONCRETE: {
				SymbolicTypeKind tk = type.typeKind();

				if (tk == SymbolicTypeKind.CHAR) {
					result.append("'");
					result.append(arguments[0].toStringBuffer(false));
					result.append("'");
				} else {
					if (!type.isNumeric() && !type.isBoolean()) {
						if (tk == SymbolicTypeKind.TUPLE)
							result.append(type.toStringBuffer(false));
						else {
							result.append('(');
							result.append(type.toStringBuffer(false));
							result.append(')');
						}
					}
					{
						SymbolicObjectKind objectKind = arguments[0]
								.symbolicObjectKind();

						if (objectKind == SymbolicObjectKind.EXPRESSION_COLLECTION) {
							@SuppressWarnings("unchecked")
							SymbolicCollection<? extends SymbolicExpression> symbolicCollection = (SymbolicCollection<? extends SymbolicExpression>) arguments[0];

							result.append("<");
							for (SymbolicExpression symbolicElement : symbolicCollection) {
								result.append(symbolicExpressionToString(
										source, state, symbolicElement, false));
								result.append(",");
							}
							result.deleteCharAt(result.length() - 1);
							result.append(">");
						} else {
							result.append(arguments[0].toStringBuffer(false));
						}

					}
					if (type.isHerbrand())
						result.append('h');
				}
				return result.toString();
			}
			case COND:
				result.append(arguments[0].toStringBuffer(true));
				result.append(" ? ");
				result.append(arguments[1].toStringBuffer(true));
				result.append(" : ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case DENSE_ARRAY_WRITE: {
				int count = 0;
				boolean first = true;

				result.append(arguments[0].toStringBuffer(true));
				result.append("[");
				for (SymbolicExpression value : (SymbolicSequence<?>) arguments[1]) {
					if (!value.isNull()) {
						if (first)
							first = false;
						else
							result.append(", ");
						result.append(count + ":=");
						result.append(symbolicExpressionToString(source, state,
								value, false));
						// result.append(value.toStringBuffer(false));
					}
					count++;
				}
				result.append("]");
				return result.toString();
			}
			case DENSE_TUPLE_WRITE: {
				int count = 0;
				boolean first = true;

				result.append(arguments[0].toStringBuffer(true));
				result.append("<");
				for (SymbolicExpression value : (SymbolicSequence<?>) arguments[1]) {
					if (!value.isNull()) {
						if (first)
							first = false;
						else
							result.append(", ");
						result.append(count + ":=");
						// result.append(value.toStringBuffer(false));
						result.append(symbolicExpressionToString(source, state,
								value, false));
					}
					count++;
				}
				result.append(">");
				return result.toString();
			}
			case DIVIDE:
				result.append(arguments[0].toStringBuffer(true));
				result.append("/");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case EQUALS:
				result.append(arguments[0].toStringBuffer(false));
				result.append(" == ");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case EXISTS:
				result.append("exists ");
				result.append(arguments[0].toStringBuffer(false));
				result.append(" : ");
				result.append(((SymbolicExpression) arguments[0]).type()
						.toStringBuffer(false));
				result.append(" . ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case FORALL:
				result.append("forall ");
				result.append(arguments[0].toStringBuffer(false));
				result.append(" : ");
				result.append(((SymbolicExpression) arguments[0]).type()
						.toStringBuffer(false));
				result.append(" . ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case INT_DIVIDE: {
				result.append(arguments[0].toStringBuffer(true));
				// result.append("\u00F7");
				result.append(" div ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			}
			case LAMBDA:
				result.append("lambda ");
				result.append(arguments[0].toStringBuffer(false));
				result.append(" : ");
				result.append(((SymbolicExpression) arguments[0]).type()
						.toStringBuffer(false));
				result.append(" . ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case LENGTH:
				result.append("length(");
				result.append(arguments[0].toStringBuffer(false));
				result.append(")");
				return result.toString();
			case LESS_THAN:
				result.append(arguments[0].toStringBuffer(false));
				result.append(" < ");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case LESS_THAN_EQUALS:
				result.append(arguments[0].toStringBuffer(false));
				result.append(" <= ");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case MODULO:
				result.append(arguments[0].toStringBuffer(true));
				result.append("%");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case MULTIPLY:
				processFlexibleBinary(source, state, symbolicExpression,
						result, "*", true, false);
				return result.toString();
			case NEGATIVE:
				result.append("-");
				result.append(arguments[0].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case NEQ:
				result.append(arguments[0].toStringBuffer(false));
				result.append(" != ");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case NOT:
				result.append("!");
				result.append(arguments[0].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case NULL:
				result.append("NULL");
				return result.toString();
			case OR:
				processFlexibleBinary(source, state, symbolicExpression,
						result, " || ", false, atomize);
				// if (atomize)
				// atomize(result);
				return result.toString();
			case POWER:
				result.append(arguments[0].toStringBuffer(true));
				result.append("^");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case SUBTRACT:
				processBinary(result, " - ", arguments[0], arguments[1], true);
				if (atomize)
					atomize(result);
				return result.toString();
			case SYMBOLIC_CONSTANT:
				result.append(arguments[0].toStringBuffer(false));
				return result.toString();
			case TUPLE_READ:
				result.append(arguments[0].toStringBuffer(true));
				result.append(".");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case TUPLE_WRITE:
				result.append(arguments[0].toStringBuffer(true));
				result.append("[.");
				result.append(arguments[1].toStringBuffer(false));
				result.append(":=");
				result.append(arguments[2].toStringBuffer(false));
				result.append("]");
				return result.toString();
			case UNION_EXTRACT:
				result.append("extract(");
				result.append(arguments[0].toStringBuffer(false));
				result.append(",");
				result.append(arguments[1].toStringBuffer(false));
				result.append(")");
				return result.toString();
			case UNION_INJECT:
				result.append("inject(");
				result.append(arguments[0].toStringBuffer(false));
				result.append(",");
				result.append(arguments[1].toStringBuffer(false));
				result.append(")");
				return result.toString();
			case UNION_TEST:
				result.append("test(");
				result.append(arguments[0].toStringBuffer(false));
				result.append(",");
				result.append(arguments[1].toStringBuffer(false));
				result.append(")");
				return result.toString();
			default:
				return symbolicExpression.toStringBufferLong().toString();
			}
		}
	}

	/**
	 * Place parentheses around the string buffer.
	 * 
	 * @param buffer
	 *            a string buffer
	 */
	private void atomize(StringBuffer buffer) {
		buffer.insert(0, '(');
		buffer.append(')');
	}

	/**
	 * Obtains the string representation of a symbolic expression which is a
	 * pointer.
	 * 
	 * @param source
	 *            The source code element of the symbolic expression
	 * @param state
	 *            The state that the given symbolic expression belongs to
	 * @param pointer
	 *            The symbolic expression that is to be evaluated
	 * @return the string representation of a symbolic expression which is a
	 *         pointer
	 */
	private String pointerValueToString(CIVLSource source, State state,
			SymbolicExpression pointer) {
		if (pointer.operator() == SymbolicOperator.NULL)
			return pointer.toString();
		else if (pointer.operator() != SymbolicOperator.CONCRETE)
			return pointer.toString();
		else {
			SymbolicTupleType pointerType = (SymbolicTupleType) pointer.type();
			int dyscopeId, vid;

			if (!pointerType.name().getString().equalsIgnoreCase("pointer")) {
				return pointer.toString();
			}

			dyscopeId = getDyscopeId(source, pointer);
			vid = getVariableId(source, pointer);
			if (dyscopeId == -1 && vid == -1)
				return "NULL";
			if (dyscopeId < 0)
				return "UNDEFINED";
			else {
				DynamicScope dyscope = state.getScope(dyscopeId);
				Variable variable = dyscope.lexicalScope().variable(vid);
				ReferenceExpression reference = (ReferenceExpression) universe
						.tupleRead(pointer, this.twoObj);

				if (variable.type().equals(this.heapType)) {
					String resultString = heapObjectReferenceToString(source,
							state.getScope(dyscopeId).identifier(),
							this.heapType, reference).third;

					return resultString;
				} else {
					StringBuffer result = new StringBuffer();

					result.append('&');
					result.append("<");
					result.append(dyscope.name());
					result.append('>');
					result.append(variable.name());
					result.append(referenceToString(source, variable.type(),
							reference).right);
					return result.toString();
				}
			}
		}
	}

	/**
	 * Obtains the string representation of a reference to a heap object or part
	 * of a heap object.
	 * 
	 * @param source
	 *            The source code element of the reference expression.
	 * @param dyscopeId
	 *            The dynamic scope ID that the heap belongs to.
	 * @param type
	 *            The static type of the expression being referenced.
	 * @param reference
	 *            The reference expression, could be:
	 *            <ol>
	 *            <li>identity reference</li>
	 *            <li>array element reference</li>
	 *            <li>tuple element reference</li>
	 *            </ol>
	 * @return the string representation of a reference to a heap object or part
	 *         of a heap object.
	 */
	private Triple<Integer, CIVLType, String> heapObjectReferenceToString(
			CIVLSource source, int dyscopeId, CIVLType type,
			ReferenceExpression reference) {
		StringBuffer result = new StringBuffer();

		if (reference.isIdentityReference()) {
			result.append("&<d");
			result.append(dyscopeId);
			result.append(">");
			result.append("heap<");
			return new Triple<>(0, type, result.toString());
		} else if (reference.isArrayElementReference()) {
			ArrayElementReference arrayEleRef = (ArrayElementReference) reference;
			Triple<Integer, CIVLType, String> parentResult = heapObjectReferenceToString(
					source, dyscopeId, type, arrayEleRef.getParent());
			NumericExpression index = arrayEleRef.getIndex();

			switch (parentResult.first) {
			case 0:
				throw new CIVLInternalException("Unreachable", source);
			case 1:
				result.append(parentResult.third);
				result.append(index);
				result.append('>');
				return new Triple<>(2, parentResult.second, result.toString());
			case 2:
				result.append(parentResult.third);
				result.append('[');
				result.append(index);
				result.append(']');
				return new Triple<>(-1, parentResult.second, result.toString());
			default:
				CIVLType arrayEleType = ((CIVLArrayType) parentResult.second)
						.elementType();

				result.append(parentResult.third);
				result.append('[');
				result.append(index);
				result.append(']');
				return new Triple<>(-1, arrayEleType, result.toString());
			}
		} else if (reference.isTupleComponentReference()) {
			TupleComponentReference tupleCompRef = (TupleComponentReference) reference;
			Triple<Integer, CIVLType, String> parentResult = heapObjectReferenceToString(
					source, dyscopeId, type, tupleCompRef.getParent());
			IntObject index = tupleCompRef.getIndex();

			switch (parentResult.first) {
			case 0:
				CIVLHeapType heapType = (CIVLHeapType) parentResult.second;
				int indexId = index.getInt();
				CIVLType heapObjType = heapType.getMalloc(indexId)
						.getStaticElementType();

				result.append(parentResult.third);
				// result.append("malloc id: ");
				result.append(index.getInt());
				result.append(',');
				return new Triple<>(1, heapObjType, result.toString());
			case 1:
			case 2:
				throw new CIVLInternalException("Unreachable", source);
			default:
				CIVLStructOrUnionType structOrUnionType = (CIVLStructOrUnionType) parentResult.second;
				StructOrUnionField field = structOrUnionType.getField(index
						.getInt());

				result.append(parentResult.third);
				result.append('.');
				result.append(field.name());
				return new Triple<>(-1, field.type(), result.toString());
			}
		} else if (reference.isUnionMemberReference()) {
			// TODO: finish this
			return null;
		} else {
			throw new CIVLInternalException("Unreachable", source);
		}
	}

	/**
	 * Obtains the string representation from a reference expression.
	 * 
	 * @param source
	 *            The source code element of the reference expression.
	 * @param type
	 *            The type of the expression being referenced.
	 * @param reference
	 *            The reference expression whose string representation is to be
	 *            obtained.
	 * @return The type of the remaining part, and the string representation of
	 *         the given reference expression.
	 */
	private Pair<CIVLType, String> referenceToString(CIVLSource source,
			CIVLType type, ReferenceExpression reference) {
		StringBuffer result = new StringBuffer();

		if (reference.isIdentityReference())
			return new Pair<>(type, result.toString());
		if (reference.isArrayElementReference()) {
			ArrayElementReference arrayEleRef = (ArrayElementReference) reference;
			Pair<CIVLType, String> parentResult = this.referenceToString(
					source, type, arrayEleRef.getParent());
			String parent = parentResult.right;
			CIVLType arrayEleType = ((CIVLArrayType) parentResult.left)
					.elementType();
			NumericExpression index = arrayEleRef.getIndex();

			result.append(parent);
			result.append('[');
			result.append(index);
			result.append(']');
			return new Pair<>(arrayEleType, result.toString());
		} else if (reference.isTupleComponentReference()) {
			TupleComponentReference tupleComponentRef = (TupleComponentReference) reference;
			IntObject index = tupleComponentRef.getIndex();
			Pair<CIVLType, String> parentResult = this.referenceToString(
					source, type, tupleComponentRef.getParent());
			String parent = parentResult.right;
			CIVLStructOrUnionType structOrUnionType = (CIVLStructOrUnionType) parentResult.left;
			StructOrUnionField field = structOrUnionType.getField(index
					.getInt());

			result.append(parent);
			result.append('.');
			result.append(field.name());
			return new Pair<CIVLType, String>(field.type(), result.toString());
		} else {
			throw new CIVLInternalException("Unreachable", source);
		}
	}

	/**
	 * Computes string representation of a binary operator expression
	 * 
	 * @param buffer
	 *            string buffer to which computed result should be appended
	 * @param opString
	 *            the string representation of the operator, e.g. "+"
	 * @param arg0
	 *            object to be represented
	 * @param arg1
	 *            object to be represented
	 * @param atomizeArgs
	 *            should each argument be atomized (surrounded by parens if
	 *            necessary)?
	 */
	private void processBinary(StringBuffer buffer, String opString,
			SymbolicObject arg0, SymbolicObject arg1, boolean atomizeArgs) {
		buffer.append(arg0.toStringBuffer(atomizeArgs));
		buffer.append(opString);
		buffer.append(arg1.toStringBuffer(atomizeArgs));
	}

	/**
	 * Computes string representation of a binary operator expression that may
	 * take either one argument (a list of expressions) or two arguments.
	 * 
	 * @param buffer
	 *            string buffer to which computed result should be appended
	 * @param opString
	 *            the string representation of the operator, e.g. "+"
	 * @param atomizeArgs
	 *            should each argument be atomized (surrounded by parens if
	 *            necessary)?
	 * @param atomizeResult
	 *            should the final result be atomized?
	 */
	private void processFlexibleBinary(CIVLSource source, State state,
			SymbolicExpression symbolicExpression, StringBuffer buffer,
			String opString, boolean atomizeArgs, boolean atomizeResult) {
		SymbolicObject[] arguments = symbolicExpression.arguments();

		if (arguments.length == 1)
			accumulate(source, state, buffer, opString,
					(SymbolicCollection<?>) arguments[0], atomizeArgs);
		else
			processBinary(buffer, opString, arguments[0], arguments[1],
					atomizeArgs);
		if (atomizeResult) {
			buffer.insert(0, '(');
			buffer.append(')');
		}
	}

	/**
	 * accumulates the operator opString to every operand in the following
	 * format opString = " " + opString + " ";
	 * 
	 * @param buffer
	 *            string buffer to which computed result should be appended
	 * @param opString
	 *            the string representation of the operator, e.g. "+"
	 * @param operands
	 *            collection of Symbolic Objects
	 * @param atomizeArgs
	 *            should each argument be atomized (surrounded by parens if
	 */
	private void accumulate(CIVLSource source, State state,
			StringBuffer buffer, String opString,
			SymbolicCollection<?> operands, boolean atomizeArgs) {
		boolean first = true;

		for (SymbolicExpression arg : operands) {
			if (first)
				first = false;
			else
				buffer.append(opString);
			buffer.append(symbolicExpressionToString(source, state, arg, first));
		}
	}

	public StringBuffer stateToString(State state) {
		int numScopes = state.numScopes();
		int numProcs = state.numProcs();
		StringBuffer result = new StringBuffer();

		result.append("State " + state.identifier());
		result.append("\n");
		result.append("| Path condition\n");
		result.append("| | " + state.getPathCondition());
		result.append("\n");
		result.append("| Dynamic scopes\n");
		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope dyscope = (ImmutableDynamicScope) state
					.getScope(i);

			if (dyscope == null)
				result.append("| | dyscope - (id=" + i + "): null\n");
			else
				result.append(dynamicScopeToString(state, dyscope, "" + i,
						"| | "));
		}
		result.append("| Process states\n");
		for (int pid = 0; pid < numProcs; pid++) {
			ProcessState process = state.getProcessState(pid);

			if (process == null)
				result.append("| | process - (id=" + pid + "): null");
			else
				result.append(process.toStringBuffer("| | "));
		}
		return result;
	}

	/**
	 * Prints a dyscope to a given print stream.
	 * 
	 * @param out
	 *            The print stream to be used for printing.
	 * @param state
	 *            The state that the dyscope belongs to.
	 * @param dyscope
	 *            The dyscope to be printed.
	 * @param id
	 *            The ID of the dyscope.
	 * @param prefix
	 *            The prefix for printing.
	 */
	private StringBuffer dynamicScopeToString(State state,
			DynamicScope dyscope, String id, String prefix) {
		Scope lexicalScope = dyscope.lexicalScope();
		int numVars = lexicalScope.numVariables();
		// BitSet reachers = dyscope.getReachers();
		// int bitSetLength = reachers.length();
		// boolean first = true;
		StringBuffer result = new StringBuffer();
		String parentString;
		DynamicScope parent = dyscope.getParent() < 0 ? null : state
				.getScope(dyscope.getParent());

		if (parent == null)
			parentString = "NULL";
		else
			parentString = parent.name();
		result.append(prefix + "dyscope " + dyscope.name() + " (id=" + id
				+ ", parent=" + parentString + ", static=" + lexicalScope.id()
				+ ")\n");
		result.append(prefix + "| variables\n");
		for (int i = 0; i < numVars; i++) {
			Variable variable = lexicalScope.variable(i);
			SymbolicExpression value = dyscope.getValue(i);
			String varName = variable.name().name();

			if (varName.equals(ModelFactory.HEAP_VAR) && value.isNull()) {
				continue;
			} else if (varName.equals(ModelFactory.ATOMIC_LOCK_VARIABLE)
					&& (value.isNull() || modelFactory.isProcessDefined(
							variable.getSource(), value).isFalse())) {
				continue;
			}
			result.append(prefix + "| | " + variable.name() + " = ");
			result.append(symbolicExpressionToString(variable.getSource(),
					state, value));
			result.append("\n");
		}
		return result;
	}

	/**
	 * Given a symbolic expression of type array of char, returns a string
	 * representation. If it is a concrete array of char consisting of concrete
	 * characters, this will be the obvious string. Otherwise the result is
	 * something readable but unspecified.
	 * 
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	public StringBuffer charArrayToString(CIVLSource source,
			SymbolicSequence<?> charArray, int startIndex, boolean forPrint) {
		StringBuffer result = new StringBuffer();
		int numChars = charArray.size();// ignoring the '\0' at the
										// end
		// of the string.
		// stringChars = new char[numChars -
		// int_arrayIndex];
		for (int j = startIndex; j < numChars; j++) {
			SymbolicExpression charExpr = charArray.get(j);
			Character theChar = universe.extractCharacter(charExpr);

			if (theChar == null)
				throw new CIVLUnimplementedFeatureException(
						"non-concrete character in string at position " + j,
						source);
			if (theChar != '\0') {
				if (forPrint) {
					String theCharToString;
					switch (theChar) {
					case '\u000C':
						theCharToString = "\\f";
						break;
					case '\u0007':
						theCharToString = "\\a";
						break;
					case '\b':
						theCharToString = "\\b";
						break;
					case '\n':
						theCharToString = "\\n";
						break;
					case '\t':
						theCharToString = "\\t";
						break;
					case '\r':
						theCharToString = "\\r";
						break;
					default:
						theCharToString = theChar.toString();
					}
					result.append(theCharToString);
				} else {
					result.append(theChar);
				}
			}
		}
		return result;
	}

	@Override
	public int getArrayIndex(CIVLSource source, SymbolicExpression charPointer) {
		int int_arrayIndex;

		if (charPointer.type() instanceof SymbolicArrayType) {
			int_arrayIndex = 0;
		} else {
			ArrayElementReference arrayRef = (ArrayElementReference) getSymRef(charPointer);
			NumericExpression arrayIndex = arrayRef.getIndex();
			int_arrayIndex = extractInt(source, arrayIndex);
		}
		return int_arrayIndex;
	}

	@Override
	public SymbolicExpression updateArrayElementReference(
			ArrayElementReference arrayReference,
			List<NumericExpression> newIndexes) {
		int dimension = newIndexes.size();
		ReferenceExpression rootParent = arrayReference;
		ReferenceExpression newRef;

		for (int i = 0; i < dimension; i++)
			rootParent = ((ArrayElementReference) rootParent).getParent();
		newRef = rootParent;
		for (int i = 0; i < dimension; i++) {
			newRef = universe.arrayElementReference(newRef, newIndexes.get(i));
		}
		return newRef;
	}

	@Override
	public SymbolicExpression arrayUnrolling(State state, String process,
			SymbolicExpression array, CIVLSource civlsource) {
		List<SymbolicExpression> unrolledElementList;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		if (array.isNull() || array == null)
			throw new CIVLInternalException("parameter array is null.",
					civlsource);

		if (array.type() instanceof SymbolicArrayType) {
			if (array.operator() == SymbolicOperator.SYMBOLIC_CONSTANT) {
				if (reasoner.extractNumber(universe.length(array)) == null)
					return array;
			}
		} else
			return universe.array(array.type(), Arrays.asList(array));

		unrolledElementList = this.arrayUnrollingWorker(state, array,
				civlsource);
		if (unrolledElementList.size() > 0)
			return universe.array(unrolledElementList.get(0).type(),
					unrolledElementList);
		else if (array instanceof SymbolicArrayType)
			return universe.emptyArray(((SymbolicArrayType) array)
					.elementType());
		else
			return universe.emptyArray(array.type());
	}

	// TODO: Too much functions about operation on arrays, do we need a sub
	// class for it?
	// Recursive helper function for arrayUnrolling, must be private.
	private List<SymbolicExpression> arrayUnrollingWorker(State state,
			SymbolicExpression array, CIVLSource civlsource) {
		BooleanExpression pathCondition = state.getPathCondition();
		List<SymbolicExpression> unrolledElementList = new LinkedList<>();
		Reasoner reasoner = universe.reasoner(pathCondition);

		if (array.isNull() || array == null)
			throw new CIVLInternalException("parameter array is null.",
					civlsource);

		if (array.operator() == SymbolicOperator.SYMBOLIC_CONSTANT) {
			if (reasoner.extractNumber(universe.length(array)) == null) {
				unrolledElementList.add(array);
				return unrolledElementList;
			}
		}

		if (array.type() instanceof SymbolicArrayType) {
			BooleanExpression claim;
			NumericExpression i = universe.zeroInt();
			NumericExpression length = universe.length(array);

			claim = universe.lessThan(i, length);
			if (((SymbolicArrayType) array.type()).elementType() instanceof SymbolicArrayType) {
				while (reasoner.isValid(claim)) {
					SymbolicExpression element = universe.arrayRead(array, i);

					unrolledElementList.addAll(arrayUnrollingWorker(state,
							element, civlsource));
					// update
					i = universe.add(i, one);
					claim = universe.lessThan(i, length);
				}
			} else {
				while (reasoner.isValid(claim)) {
					SymbolicExpression element = universe.arrayRead(array, i);

					unrolledElementList.add(element);
					// update
					i = universe.add(i, one);
					claim = universe.lessThan(i, length);
				}
			}
		} else {
			unrolledElementList.add(array);
		}
		return unrolledElementList;
	}

	@Override
	public SymbolicExpression arrayCasting(State state, String process,
			SymbolicExpression oldArray, SymbolicType type,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		BooleanExpression pathCondition = state.getPathCondition();
		Reasoner reasoner = universe.reasoner(pathCondition);

		if (oldArray.type().equals(type))
			return oldArray;
		if (!(oldArray.type() instanceof SymbolicArrayType)
				&& !(type instanceof SymbolicArrayType))
			return oldArray;
		else if (!(type instanceof SymbolicArrayType)) {
			if (reasoner
					.isValid(universe.equals(universe.length(oldArray), one))) {
				return universe.arrayRead(oldArray, zero);
			} else {
				return oldArray;
			}
		} else {
			SymbolicType elementType = ((SymbolicArrayType) type).elementType();
			NumericExpression i = universe.zeroInt();
			NumericExpression dimensionLength; // length of current dimension
			NumericExpression chunkLength; // (the unrolled old array length) /
											// (dimensionLength)
			NumericExpression subEndIndex, subStartIndex;
			List<SymbolicExpression> newElements = new LinkedList<>();
			SymbolicExpression unrolledArray;
			SymbolicExpression subArray;
			BooleanExpression claim;

			// ------Cast the oldArray to an array of the compatible new type
			if (!((SymbolicArrayType) type).isComplete()) {
				// ------For incomplete array type, only 1-d array type is
				// allowed.
				// ------Unrolling old array
				return this
						.arrayUnrolling(state, process, oldArray, civlsource);
			}
			// ------For complete array, we have to compute recursively.
			dimensionLength = ((SymbolicCompleteArrayType) type).extent();
			claim = universe.lessThan(i, dimensionLength);
			unrolledArray = this.arrayUnrolling(state, process, oldArray,
					civlsource);
			chunkLength = universe.divide(universe.length(unrolledArray),
					dimensionLength);
			subStartIndex = i;
			subEndIndex = chunkLength;
			while (reasoner.isValid(claim)) {
				subArray = this.getSubArray(unrolledArray, subStartIndex,
						subEndIndex, state, process, civlsource);
				newElements.add(this.arrayCasting(state, process, subArray,
						elementType, civlsource));
				i = universe.add(i, one);
				subStartIndex = subEndIndex;
				subEndIndex = universe.add(chunkLength, chunkLength);
				claim = universe.lessThan(i, dimensionLength);
			}
			return universe.array(newElements.get(0).type(), newElements);
		}
		//throw new CIVLInternalException("Array casting failed", civlsource);
	}

	@Override
	public SymbolicExpression rangeOfDomainAt(SymbolicExpression domain,
			int index) {
		return universe.tupleRead(domain, universe.intObject(index));
	}

	@Override
	public SymbolicExpression initialValueOfRange(SymbolicExpression range,
			boolean isLast) {
		SymbolicExpression low = universe.tupleRead(range, zeroObj);
		SymbolicExpression step = universe.tupleRead(range, twoObj);

		if (isLast)
			return universe.subtract((NumericExpression) low,
					(NumericExpression) step);
		return low;
	}

	@Override
	public BooleanExpression isInRange(SymbolicExpression value,
			SymbolicExpression domain, int index) {
		SymbolicExpression range = universe.tupleRead(domain,
				universe.intObject(index));
		SymbolicExpression high = universe.tupleRead(range, oneObj);
		SymbolicExpression step = universe.tupleRead(range, twoObj);
		BooleanExpression positiveStep = universe.lessThan(zero,
				(NumericExpression) step);
		BooleanExpression negativeStep = universe.lessThan(
				(NumericExpression) step, zero);
		BooleanExpression positiveStepResult = universe.and(positiveStep,
				universe.lessThanEquals((NumericExpression) value,
						(NumericExpression) high));
		BooleanExpression negativeStepResult = universe.and(negativeStep,
				universe.lessThanEquals((NumericExpression) high,
						(NumericExpression) value));

		if (positiveStep.isTrue())
			return universe.lessThanEquals((NumericExpression) value,
					(NumericExpression) high);
		if (negativeStep.isTrue())
			return universe.lessThanEquals((NumericExpression) high,
					(NumericExpression) value);
		return universe.or(positiveStepResult, negativeStepResult);
	}

	@Override
	public SymbolicExpression rangeIncremental(SymbolicExpression value,
			SymbolicExpression range) {
		NumericExpression step = (NumericExpression) universe.tupleRead(range,
				twoObj);

		return universe.add((NumericExpression) value, step);
	}

	@Override
	public SymbolicExpression getLowOfDomainAt(SymbolicExpression domain,
			int index) {
		SymbolicExpression range = universe.tupleRead(domain,
				universe.intObject(index));

		return universe.tupleRead(range, zeroObj);
	}

	@Override
	public NumericExpression getRangeSize(SymbolicExpression range) {
		NumericExpression low = (NumericExpression) universe.tupleRead(range,
				this.zeroObj);
		NumericExpression high = (NumericExpression) universe.tupleRead(range,
				oneObj);
		NumericExpression step = (NumericExpression) universe.tupleRead(range,
				this.twoObj);
		NumericExpression size = universe.subtract(high, low);
		NumericExpression remainder = universe.modulo(size, step);

		size = universe.subtract(size, remainder);
		size = universe.divide(size, step);
		size = universe.add(size, this.one);
		return size;
	}

	@Override
	public NumericExpression getLowOfRange(SymbolicExpression range) {
		return (NumericExpression) universe.tupleRead(range, zeroObj);
	}

	@Override
	public NumericExpression getHighOfRange(SymbolicExpression range) {
		return (NumericExpression) universe.tupleRead(range, oneObj);
	}

	@Override
	public NumericExpression getStepOfRange(SymbolicExpression range) {
		return (NumericExpression) universe.tupleRead(range, twoObj);
	}

	@Override
	public boolean isInitialized(SymbolicExpression value) {
		if (value.isNull())
			return false;
		return true;
	}

	/**
	 * A pointer can be only concrete for the current implementation of CIVL,
	 * because the only way to make one is through <code>$malloc</code> or
	 * <code>&</code>.
	 */
	@Override
	public SymbolicExpression contains(SymbolicExpression pointer1,
			SymbolicExpression pointer2) {
		ReferenceExpression ref1 = (ReferenceExpression) universe.tupleRead(
				pointer1, twoObj);
		ReferenceExpression ref2 = (ReferenceExpression) universe.tupleRead(
				pointer2, twoObj);
		SymbolicExpression scope1 = universe.tupleRead(pointer1, zeroObj);
		SymbolicExpression scope2 = universe.tupleRead(pointer2, zeroObj);
		SymbolicExpression vid1 = universe.tupleRead(pointer1, oneObj);
		SymbolicExpression vid2 = universe.tupleRead(pointer2, oneObj);
		List<ReferenceExpression> refComps1 = new ArrayList<>();
		List<ReferenceExpression> refComps2 = new ArrayList<>();
		int numRefs1, numRefs2, offset;
		BooleanExpression result = this.trueValue;

		if (ref1.isIdentityReference() && ref2.isIdentityReference()) {
			return universe.canonic(universe.equals(ref1, ref2));
		}
		if (ref2.isIdentityReference() // second contains first
				|| universe.equals(scope1, scope2).isFalse() // different scope
																// id
				|| universe.equals(vid1, vid2).isFalse()) // different vid
			return this.falseValue;
		if (ref1.isIdentityReference() && !ref2.isIdentityReference())
			return this.trueValue;
		numberRefs(ref1, refComps1);
		numberRefs(ref2, refComps2);
		numRefs1 = refComps1.size();
		numRefs2 = refComps2.size();
		if (numRefs1 > numRefs2)
			return this.falseValue;
		offset = numRefs2 - numRefs1;
		for (int i = offset; i < numRefs1; i++) {
			result = universe.and(result, universe.equals(refComps1.get(i),
					refComps2.get(i + offset)));
		}
		return result;
	}

	private void numberRefs(ReferenceExpression ref,
			List<ReferenceExpression> components) {
		ReferenceKind kind = ref.referenceKind();

		switch (kind) {
		case ARRAY_ELEMENT:
			ArrayElementReference arrayRef = (ArrayElementReference) ref;

			components.add(arrayRef);
			numberRefs(arrayRef.getParent(), components);
			break;
		case TUPLE_COMPONENT:
			TupleComponentReference tupleRef = (TupleComponentReference) ref;

			components.add(tupleRef);
			numberRefs(tupleRef.getParent(), components);
			break;
		case UNION_MEMBER:
			UnionMemberReference unionRef = (UnionMemberReference) ref;

			components.add(unionRef);
			numberRefs(unionRef.getParent(), components);
			break;
		default:
			return;
		}
	}

	@Override
	public boolean isNullPointer(SymbolicExpression pointer) {
		return universe.equals(this.nullPointer, pointer).isTrue();
	}

	@Override
	public boolean isHeapObjectDefined(SymbolicExpression heapObj) {
		if (heapObj.numArguments() > 0
				&& heapObj.argument(0) instanceof SymbolicConstant) {
			SymbolicConstant value = (SymbolicConstant) heapObj.argument(0);

			if (value.name().getString().equals("UNDEFINED"))
				return false;
		} else if (heapObj instanceof SymbolicConstant) {
			SymbolicConstant value = (SymbolicConstant) heapObj;

			if (value.name().getString().equals("UNDEFINED"))
				return false;
		}
		return true;
	}

	@Override
	public boolean isHeapPointer(SymbolicExpression pointer) {
		int dyscopeID = this.getDyscopeId(null, pointer);
		int vid = this.getVariableId(null, pointer);

		if (dyscopeID < 0)
			return false;
		return vid == 0;
	}

	@Override
	public SymbolicExpression heapPointer(CIVLSource source, State state,
			String process, SymbolicExpression scopeValue)
			throws UnsatisfiablePathConditionException {
		if (scopeValue.operator() == SymbolicOperator.SYMBOLIC_CONSTANT) {
			errorLogger.logSimpleError(source, state, process,
					stateToString(state), ErrorKind.OTHER,
					"Attempt to get the heap pointer of a symbolic scope");
			throw new UnsatisfiablePathConditionException();
		} else {
			int dyScopeID = modelFactory.getScopeId(source, scopeValue);
			ReferenceExpression symRef = (ReferenceExpression) universe
					.canonic(universe.identityReference());

			if (dyScopeID < 0) {
				errorLogger.logSimpleError(source, state, process,
						stateToString(state), ErrorKind.MEMORY_LEAK,
						"Attempt to access the heap of the scope that has been "
								+ "removed from state");
				throw new UnsatisfiablePathConditionException();
			} else {
				DynamicScope dyScope = state.getScope(dyScopeID);
				Variable heapVariable = dyScope.lexicalScope().variable(
						"__heap");

				if (heapVariable == null) {
					errorLogger.logSimpleError(source, state, process,
							stateToString(state), ErrorKind.MEMORY_LEAK,
							"Attempt to access a heap that never exists");
					throw new UnsatisfiablePathConditionException();
				}
				return makePointer(dyScopeID, heapVariable.vid(), symRef);
			}
		}
	}

	/**
	 * A heap object pointer shall have the form of: <code>&<dn,i,j>[0]</code>
	 */
	@Override
	public boolean isHeapObjectPointer(CIVLSource source,
			SymbolicExpression pointer) {
		ReferenceExpression ref = this.getSymRef(pointer);
		ArrayElementReference arrayEleRef;

		if (!ref.isArrayElementReference())
			return false;
		arrayEleRef = (ArrayElementReference) ref;
		if (!arrayEleRef.getIndex().isZero())
			return false;
		ref = arrayEleRef.getParent();
		if (!ref.isArrayElementReference())
			return false;
		ref = ((ArrayElementReference) ref).getParent();
		if (!ref.isTupleComponentReference())
			return false;
		ref = ((TupleComponentReference) ref).getParent();
		if (ref.isIdentityReference())
			return true;
		return false;
	}

	@Override
	public SymbolicExpression heapCellPointer(
			SymbolicExpression heapObjectPointer) {
		ArrayElementReference arrayEleRef = (ArrayElementReference) universe
				.tupleRead(heapObjectPointer, twoObj);
		ReferenceExpression ref = arrayEleRef.getParent();

		return universe.tuple(
				pointerType,
				Arrays.asList(new SymbolicExpression[] {
						universe.tupleRead(heapObjectPointer, zeroObj),
						universe.tupleRead(heapObjectPointer, oneObj), ref }));
	}

	@Override
	public ReferenceExpression referenceOfPointer(SymbolicExpression pointer) {
		ReferenceExpression ref = (ReferenceExpression) universe.tupleRead(
				pointer, twoObj);

		if (this.isHeapPointer(pointer)) {
			return heapReference(ref).left;
		} else
			return ref;
	}

	private Pair<ReferenceExpression, Integer> heapReference(
			ReferenceExpression ref) {
		if (ref.isIdentityReference())
			return new Pair<>(ref, 0);
		else {
			ReferenceExpression parentRef;
			Pair<ReferenceExpression, Integer> parent;

			if (ref.isArrayElementReference())
				parentRef = ((ArrayElementReference) ref).getParent();
			else if (ref.isTupleComponentReference())
				parentRef = ((TupleComponentReference) ref).getParent();
			else
				parentRef = ((UnionMemberReference) ref).getParent();
			parent = heapReference(parentRef);
			if (parent.right < 3)
				return new Pair<>(ref, parent.right + 1);
			else {
				ReferenceExpression newRef;

				if (parent.right == 3)
					parentRef = universe.identityReference();
				else
					parentRef = parent.left;
				if (ref.isArrayElementReference()) {
					newRef = universe.arrayElementReference(parentRef,
							((ArrayElementReference) ref).getIndex());
				} else if (ref.isTupleComponentReference())
					newRef = universe.tupleComponentReference(parentRef,
							((TupleComponentReference) ref).getIndex());
				else
					newRef = universe.unionMemberReference(parentRef,
							((UnionMemberReference) ref).getIndex());
				return new Pair<>(newRef, 4);
			}
		}
	}

	@Override
	public SymbolicExpression makePointer(SymbolicExpression objectPointer,
			ReferenceExpression reference) {
		ReferenceExpression objRef = (ReferenceExpression) universe.tupleRead(
				objectPointer, twoObj);
		SymbolicExpression scope = universe.tupleRead(objectPointer, zeroObj);
		SymbolicExpression vid = universe.tupleRead(objectPointer, oneObj);

		if (!objRef.isIdentityReference())
			reference = makeParentOf(objRef, reference);
		return universe
				.tuple(pointerType, Arrays.asList(scope, vid, reference));
	}

	private ReferenceExpression makeParentOf(ReferenceExpression parent,
			ReferenceExpression ref) {
		if (ref.isIdentityReference())
			return parent;
		else if (ref.isArrayElementReference()) {
			ArrayElementReference arrayEle = (ArrayElementReference) ref;
			ReferenceExpression myParent = makeParentOf(parent,
					arrayEle.getParent());

			return universe
					.arrayElementReference(myParent, arrayEle.getIndex());
		} else if (ref.isTupleComponentReference()) {
			TupleComponentReference arrayEle = (TupleComponentReference) ref;
			ReferenceExpression myParent = makeParentOf(parent,
					arrayEle.getParent());

			return universe.tupleComponentReference(myParent,
					arrayEle.getIndex());
		} else {
			UnionMemberReference arrayEle = (UnionMemberReference) ref;
			ReferenceExpression myParent = makeParentOf(parent,
					arrayEle.getParent());

			return universe.unionMemberReference(myParent, arrayEle.getIndex());
		}
	}

	@Override
	public boolean isValidRefOf(ReferenceExpression ref,
			SymbolicExpression value) {
		return isValidRefOfValue(ref, value).right;
	}

	private Pair<SymbolicExpression, Boolean> isValidRefOfValue(
			ReferenceExpression ref, SymbolicExpression value) {
		if (ref.isIdentityReference())
			return new Pair<>(value, true);
		else if (ref.isArrayElementReference()) {
			ArrayElementReference arrayEleRef = (ArrayElementReference) ref;
			SymbolicExpression targetValue;
			Pair<SymbolicExpression, Boolean> parentTest = isValidRefOfValue(
					arrayEleRef.getParent(), value);

			if (!parentTest.right)
				return new Pair<>(value, false);
			targetValue = parentTest.left;
			if (!(targetValue.type() instanceof SymbolicArrayType))
				return new Pair<>(targetValue, false);
			return new Pair<>(universe.arrayRead(targetValue,
					arrayEleRef.getIndex()), true);
		} else if (ref.isTupleComponentReference()) {
			TupleComponentReference tupleCompRef = (TupleComponentReference) ref;
			SymbolicExpression targetValue;
			Pair<SymbolicExpression, Boolean> parentTest = isValidRefOfValue(
					tupleCompRef.getParent(), value);

			if (!parentTest.right)
				return new Pair<>(value, false);
			targetValue = parentTest.left;
			if (!(targetValue.type() instanceof SymbolicTupleType))
				return new Pair<>(targetValue, false);
			return new Pair<>(universe.tupleRead(targetValue,
					tupleCompRef.getIndex()), true);
		} else {// UnionMemberReference
			UnionMemberReference unionMemRef = (UnionMemberReference) ref;
			SymbolicExpression targetValue;
			Pair<SymbolicExpression, Boolean> parentTest = isValidRefOfValue(
					unionMemRef.getParent(), value);

			if (!parentTest.right)
				return new Pair<>(value, false);
			targetValue = parentTest.left;
			if (!(targetValue.type() instanceof SymbolicUnionType))
				return new Pair<>(targetValue, false);
			return new Pair<>(universe.unionExtract(unionMemRef.getIndex(),
					targetValue), true);
		}
	}

	@Override
	public CIVLType typeOfObjByPointer(CIVLSource soruce, State state,
			SymbolicExpression pointer) {
		ReferenceExpression reference = this.getSymRef(pointer);
		int dyscopeId = getDyscopeId(soruce, pointer);
		int vid = getVariableId(soruce, pointer);
		CIVLType varType = state.getScope(dyscopeId).lexicalScope()
				.variable(vid).type();

		return typeOfObjByRef(varType, reference);
	}

	private CIVLType typeOfObjByRef(CIVLType type, ReferenceExpression ref) {
		if (ref.isIdentityReference())
			return type;
		else if (ref.isArrayElementReference()) {
			ArrayElementReference arrayEleRef = (ArrayElementReference) ref;
			CIVLType parentType = typeOfObjByRef(type, arrayEleRef.getParent());

			if (parentType.isDomainType())
				return modelFactory.rangeType();
			return ((CIVLArrayType) parentType).elementType();
		} else {
			int index;
			CIVLType parentType;
			ReferenceExpression parent;

			if (ref.isTupleComponentReference()) {
				TupleComponentReference tupleCompRef = (TupleComponentReference) ref;

				index = tupleCompRef.getIndex().getInt();
				parent = tupleCompRef.getParent();
			} else {
				// UnionMemberReference
				UnionMemberReference unionMemRef = (UnionMemberReference) ref;

				index = unionMemRef.getIndex().getInt();
				parent = unionMemRef.getParent();
			}
			parentType = typeOfObjByRef(type, parent);
			if (parentType.isHeapType()) {
				CIVLArrayType heapTupleType = modelFactory
						.incompleteArrayType(((CIVLHeapType) parentType)
								.getMalloc(index).getStaticElementType());

				heapTupleType = modelFactory.incompleteArrayType(heapTupleType);
				return heapTupleType;
			}
			return ((CIVLStructOrUnionType) parentType).getField(index).type();
		}
	}

	@Override
	public boolean isDisjointWith(SymbolicExpression pointer1,
			SymbolicExpression pointer2) {
		if (pointer1.equals(pointer2))
			return false;
		{
			SymbolicExpression scope1 = universe.tupleRead(pointer1, zeroObj), var1 = universe
					.tupleRead(pointer1, oneObj);
			SymbolicExpression scope2 = universe.tupleRead(pointer2, zeroObj), var2 = universe
					.tupleRead(pointer2, oneObj);
			ReferenceExpression ref1 = (ReferenceExpression) universe
					.tupleRead(pointer1, twoObj);
			ReferenceExpression ref2 = (ReferenceExpression) universe
					.tupleRead(pointer2, twoObj);

			if (!scope1.equals(scope2))
				return true;
			if (!var1.equals(var2))
				return true;
			if (ref1.equals(ref2))
				return false;
			return isDisjoint(ref1, ref2);
		}
	}

	private boolean isDisjoint(ReferenceExpression ref1,
			ReferenceExpression ref2) {
		List<ReferenceExpression> ancestors1, ancestors2;
		int numAncestors1, numAncestors2, minNum;

		ancestors1 = this.ancestorsOfRef(ref1);
		ancestors2 = this.ancestorsOfRef(ref2);
		numAncestors1 = ancestors1.size();
		numAncestors2 = ancestors2.size();
		minNum = numAncestors1 <= numAncestors2 ? numAncestors1 : numAncestors2;
		for (int i = 0; i < minNum; i++) {
			ReferenceExpression ancestor1 = ancestors1.get(i), ancestor2 = ancestors2
					.get(i);

			if (!ancestor1.equals(ancestor2))
				return true;
		}
		return false;
	}

	// private Triple<Boolean, List<ReferenceExpression>,
	// List<ReferenceExpression>> isDisjoint( ReferenceExpression re1,
	// ReferenceExpression ref2
	// List<ReferenceExpression> refs1, List<ReferenceExpression> refs2) {
	// if (ref1.isIdentityReference() && ref2.isIdentityReference())
	// return new Triple<>(false, ref1, ref2);
	// else {
	// ReferenceExpression parent1, parent2;
	// ReferenceKind kind1 = ref1.referenceKind(), kind2 = ref2
	// .referenceKind();
	// Triple<Boolean, ReferenceExpression, ReferenceExpression> parentResult;
	//
	// if (kind1 == ReferenceKind.IDENTITY)
	// parent1 = ref1;
	// else if (kind1 == ReferenceKind.ARRAY_ELEMENT)
	// parent1 = ((ArrayElementReference) ref1).getParent();
	// else if (kind1 == ReferenceKind.TUPLE_COMPONENT)
	// parent1 = ((TupleComponentReference) ref1).getParent();
	// else
	// parent1 = ((UnionMemberReference) ref1).getParent();
	// if (kind2 == ReferenceKind.IDENTITY)
	// parent2 = ref2;
	// else if (kind2 == ReferenceKind.ARRAY_ELEMENT)
	// parent2 = ((ArrayElementReference) ref2).getParent();
	// else if (kind2 == ReferenceKind.TUPLE_COMPONENT)
	// parent2 = ((TupleComponentReference) ref2).getParent();
	// else
	// parent2 = ((UnionMemberReference) ref2).getParent();
	// parentResult = isDisjoint(parent1, parent2);
	// if (parentResult.first || kind1 != kind2)
	// return new Triple<>(true, null, null);
	// if (kind1 == ReferenceKind.ARRAY_ELEMENT) {
	// NumericExpression index1 = ((ArrayElementReference) ref1)
	// .getIndex(), index2 = ((ArrayElementReference) ref2)
	// .getIndex();
	//
	// if (!index1.equals(index2))
	// return new Triple<>(true, null, null);
	// else return new Triple<>(false, )
	// }
	//
	// }
	//
	// // if (ref1.isIdentityReference()) {
	// // return new Triple<>(false, ref1, ref1);
	// // } else if (ref2.isIdentityReference())
	// // return new Triple<>(false, ref2, ref2);
	// // else {
	// //
	// // if (!kind1.equals(kind2))
	// // return new Triple<>(true, null, null);
	// // else {
	// // if(kind1 == ReferenceKind.ARRAY_ELEMENT){
	// // NumericExpression index1 = ((ArrayElementReference) ref1).getIndex(),
	// // index2 = ((ArrayElementReference) ref2).getIndex();
	// //
	// // if(kind1 )
	// // }
	// // }
	// // }
	// return null;
	// }

	private List<ReferenceExpression> ancestorsOfRef(ReferenceExpression ref) {
		if (ref.isIdentityReference())
			return new ArrayList<>();
		else {
			ReferenceKind kind = ref.referenceKind();
			ReferenceExpression parent;
			List<ReferenceExpression> result;

			switch (kind) {
			case ARRAY_ELEMENT:
				parent = ((ArrayElementReference) ref).getParent();
				break;
			case TUPLE_COMPONENT:
				parent = ((TupleComponentReference) ref).getParent();
				break;
			default:// UnionMember
				parent = ((UnionMemberReference) ref).getParent();
			}
			result = ancestorsOfRef(parent);
			result.add(ref);
			return result;
		}
	}
}
