package edu.udel.cis.vsl.civl.semantics.common;

import java.math.BigInteger;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.AbstractFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression.LHSExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AtomicLockAssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlParForSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.DomainIteratorStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnit;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableDynamicScope;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.OffsetReference;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.expr.UnionMemberReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

public class CommonSymbolicAnalyzer implements SymbolicAnalyzer {

	/* *************************** Instance Fields ************************* */

	private final String SEF_START = "[";
	private final String SEF = ":=";
	private final String SEF_END = "]";

	private CIVLErrorLogger errorLogger;

	private ModelFactory modelFactory;

	private CIVLTypeFactory typeFactory;

	/**
	 * The pointer value is a triple <s,v,r> where s identifies the dynamic
	 * scope, v identifies the variable within that scope, and r identifies a
	 * point within that variable. The type of s is scopeType, which is just a
	 * tuple wrapping a single integer which is the dynamic scope ID number. The
	 * type of v is integer; it is the (static) variable ID number for the
	 * variable in its scope. The type of r is ReferenceExpression from SARL.
	 */
	private SymbolicTupleType pointerType;

	private SymbolicUtility symbolicUtil;

	private SymbolicUniverse universe;

	private NumericExpression zero;

	private IntObject oneObj;

	private CIVLHeapType heapType;

	private SymbolicTupleType dynamicHeapType;

	private SymbolicTupleType procType;

	private SymbolicTupleType scopeType;

	private SymbolicTupleType functionPointerType;
	private Evaluator evaluator;

	@SuppressWarnings("unused")
	private CIVLConfiguration config;

	/* ***************************** Constructors ************************** */

	public CommonSymbolicAnalyzer(CIVLConfiguration config,
			SymbolicUniverse universe, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil) {
		this.universe = universe;
		this.modelFactory = modelFactory;
		this.typeFactory = modelFactory.typeFactory();
		this.symbolicUtil = symbolicUtil;
		pointerType = typeFactory.pointerSymbolicType();
		this.heapType = typeFactory.heapType();
		this.dynamicHeapType = typeFactory.heapSymbolicType();
		this.procType = this.typeFactory.processSymbolicType();
		this.scopeType = this.typeFactory.scopeSymbolicType();
		this.functionPointerType = typeFactory.functionPointerSymbolicType();
		this.oneObj = (IntObject) universe.canonic(universe.intObject(1));
		// this.twoObj = (IntObject) universe.canonic(universe.intObject(2));
		zero = (NumericExpression) universe.canonic(universe.integer(0));
		this.config = config;
	}

	/* ******************** Methods From SymbolicAnalyzer ****************** */

	@Override
	public SymbolicUniverse getUniverse() {
		return universe;
	}

	@Override
	public ReferenceExpression getMemBaseReference(State state,
			SymbolicExpression pointer, CIVLSource source) {
		CIVLType objType;
		ReferenceExpression ref = symbolicUtil.getSymRef(pointer);
		int vid;

		vid = symbolicUtil.getVariableId(source, pointer);
		// If the pointer is pointing to an memory space, then no need to
		// continue casting because there won't be any multi-dimensional array
		// and "&a" and "a" when "a" is a pointer to a memory space is
		// different.
		if (vid == 0)
			return ref;
		objType = typeOfObjByPointer(source, state, pointer);
		while (objType.isArrayType()) {
			ref = universe.arrayElementReference(ref, zero);
			objType = ((CIVLArrayType) objType).elementType();
		}
		return ref;
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
						this.stateInformation(state), claim, valid,
						ErrorKind.OUT_OF_BOUNDS, "negative start index");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(endIndex, length);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = errorLogger.logError(source, state, process,
						this.stateInformation(state), claim, valid,
						ErrorKind.OUT_OF_BOUNDS,
						"end index exceeds length of array");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(startIndex, endIndex);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = errorLogger.logError(source, state, process,
						this.stateInformation(state), claim, valid,
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
	public StringBuffer stateToString(State state) {
		return stateToString(state, -1, -1);
	}

	@Override
	public StringBuffer stateToString(State state, int lastSavedState,
			int sequenceId) {
		int numScopes = state.numDyscopes();
		int numProcs = state.numProcs();
		StringBuffer result = new StringBuffer();
		int canonicId = state.getCanonicId();

		result.append("State ");
		if (canonicId != -1)
			result.append(canonicId);
		else if (lastSavedState != -1)
			result.append(lastSavedState + "." + sequenceId);
		else
			result.append(state.identifier());
		result.append("\n");
		result.append("| Path condition");
		result.append(this.pathconditionToString(null, state, "| | ",
				state.getPathCondition()));
		// result.append("| | "
		// + this.symbolicExpressionToString(null, state, null,
		// state.getPathCondition()));
		result.append("\n");
		result.append("| Dynamic scopes\n");
		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope dyscope = (ImmutableDynamicScope) state
					.getDyscope(i);

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
				result.append("| | process - (id=" + pid + "): null\n");
			else
				result.append(process.toStringBuffer("| | "));
		}
		return result;
	}

	@Override
	public String symbolicExpressionToString(CIVLSource source, State state,
			CIVLType type, SymbolicExpression symbolicExpression) {
		return this.symbolicExpressionToString(source, state, type,
				symbolicExpression, "", "| ").toString();
	}

	@Override
	public CIVLType typeOfObjByPointer(CIVLSource soruce, State state,
			SymbolicExpression pointer) {
		ReferenceExpression reference = this.symbolicUtil.getSymRef(pointer);
		int dyscopeId = symbolicUtil.getDyscopeId(soruce, pointer);
		int vid = symbolicUtil.getVariableId(soruce, pointer);
		CIVLType varType = state.getDyscope(dyscopeId).lexicalScope()
				.variable(vid).type();

		return typeOfObjByRef(varType, reference);
	}

	@Override
	public CIVLType getArrayBaseType(State state, CIVLSource source,
			SymbolicExpression arrayPtr) {
		CIVLType type = this.typeOfObjByPointer(source, state, arrayPtr);

		while (type instanceof CIVLArrayType)
			type = ((CIVLArrayType) type).elementType();
		return type;
	}

	/* *************************** Private Methods ************************* */

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
	 */
	private void accumulate(CIVLSource source, State state,
			StringBuffer buffer, String opString, SymbolicSequence<?> operands) {
		boolean first = true;

		for (SymbolicExpression arg : operands) {
			if (first)
				first = false;
			else
				buffer.append(opString);
			buffer.append(symbolicExpressionToString(source, state, null, arg,
					true, "", ""));
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
		int parentId = dyscope.getParent();

		if (parentId < 0)
			parentString = "NULL";
		else
			parentString = "d" + dyscope.getParent();
		result.append(prefix + "dyscope d" + id + " (parent=" + parentString
				+ ", static=" + lexicalScope.id() + ")\n");
		result.append(prefix + "| variables\n");
		for (int i = 0; i < numVars; i++) {
			Variable variable = lexicalScope.variable(i);
			SymbolicExpression value = dyscope.getValue(i);
			String varName = variable.name().name();

			if (varName.equals(ModelConfiguration.HEAP_VAR) && value.isNull()) {
				continue;
			} else if (varName.equals(ModelConfiguration.TIME_COUNT_VARIABLE)
					|| varName
							.equals(ModelConfiguration.SYMBOLIC_CONSTANT_COUNTER)
					|| varName
							.equals(ModelConfiguration.SYMBOLIC_INPUT_COUNTER)) {
				continue;
			} else if (varName.equals(ModelConfiguration.ATOMIC_LOCK_VARIABLE)
					&& (value.isNull() || !modelFactory
							.isPocessIdDefined(modelFactory.getProcessId(
									variable.getSource(), value)))) {
				continue;
			}
			result.append(prefix + "| | " + variable.name());
			// if (variable.type().areSubtypesScalar())
			result.append(" = ");
			result.append(symbolicExpressionToString(variable.getSource(),
					state, variable.type(), value, prefix + "| | ", "| "));
			result.append("\n");
		}
		return result;
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
	private StringBuffer functionPointerValueToString(CIVLSource source,
			State state, SymbolicExpression pointer) {
		StringBuffer result = new StringBuffer();

		if (pointer.operator() == SymbolicOperator.NULL
				|| pointer.operator() != SymbolicOperator.TUPLE)
			return result.append(pointer);
		else {
			int dyscopeId = this.symbolicUtil.getDyscopeId(source, pointer);

			if (dyscopeId < 0)
				result.append("UNDEFINED");
			else {
				DynamicScope dyScope = state.getDyscope(dyscopeId);
				NumericExpression funcIdExpr = (NumericExpression) universe
						.tupleRead(pointer, oneObj);
				int fid = symbolicUtil.extractInt(source, funcIdExpr);
				CIVLFunction function = dyScope.lexicalScope().getFunction(fid);

				result.append("&<");
				result.append("d" + dyscopeId);
				result.append(">");
				result.append(function.toString());
			}
			return result;
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
	 *            <li>tuple component reference</li>
	 *            <li>union member reference</li>
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
			result.append("heap.malloc");
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
				result.append(']');
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
		} else {
			ReferenceExpression parent;
			IntObject index;
			Triple<Integer, CIVLType, String> parentResult;

			if (reference.isTupleComponentReference()) {
				TupleComponentReference tupleCompRef = (TupleComponentReference) reference;

				parent = tupleCompRef.getParent();
				index = tupleCompRef.getIndex();
			} else {
				UnionMemberReference unionMemRef = (UnionMemberReference) reference;

				parent = unionMemRef.getParent();
				index = unionMemRef.getIndex();
			}
			parentResult = heapObjectReferenceToString(source, dyscopeId, type,
					parent);

			switch (parentResult.first) {
			case 0:
				CIVLHeapType heapType = (CIVLHeapType) parentResult.second;
				int indexId = index.getInt();
				CIVLType heapObjType = heapType.getMalloc(indexId)
						.getStaticElementType();

				result.append(parentResult.third);
				result.append(index.getInt());
				result.append('[');
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
		}
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
	private void processFlexibleBinaryNew(CIVLSource source, State state,
			SymbolicExpression symbolicExpression, StringBuffer buffer,
			String opString, boolean atomizeArgs, boolean atomizeResult) {
		int numArgs = symbolicExpression.numArguments();
		boolean first = true;

		for (int i = 0; i < numArgs; i++) {
			SymbolicObject arg = symbolicExpression.argument(i);
			String argString;

			if (arg instanceof SymbolicExpression)
				argString = this.symbolicExpressionToString(source, state,
						null, (SymbolicExpression) arg, true, "", "")
						.toString();
			else
				argString = symbolicExpression.argument(i)
						.toStringBuffer(atomizeArgs).toString();
			if (!first && (!opString.equals("+") || !argString.startsWith("-"))) {
				buffer.append(opString);
			}
			buffer.append(argString);
			if (first)
				first = false;
		}
		if (atomizeResult) {
			buffer.insert(0, '(');
			buffer.append(')');
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
		int numArgs = symbolicExpression.numArguments();

		if (numArgs == 1)
			accumulate(source, state, buffer, opString,
					(SymbolicSequence<?>) symbolicExpression.argument(0));
		else
			processBinary(buffer, opString, symbolicExpression.argument(0),
					symbolicExpression.argument(1), true);
		if (atomizeResult) {
			buffer.insert(0, '(');
			buffer.append(')');
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

			if (!parentResult.left.isStructType())
				return parentResult;

			CIVLStructOrUnionType structOrUnionType = (CIVLStructOrUnionType) parentResult.left;
			StructOrUnionField field = structOrUnionType.getField(index
					.getInt());

			result.append(parent);
			result.append('.');
			result.append(field.name());
			return new Pair<CIVLType, String>(field.type(), result.toString());
		} else if (reference.isOffsetReference()) {
			OffsetReference offsetRef = (OffsetReference) reference;
			NumericExpression offset = offsetRef.getOffset();
			Pair<CIVLType, String> parentResult = this.referenceToString(
					source, type, offsetRef.getParent());
			String parent = parentResult.right;

			result.append(parent);
			result.append('+');
			result.append(offset.atomString());
			return new Pair<CIVLType, String>(parentResult.left,
					result.toString());
		} else {
			throw new CIVLInternalException("Unreachable", source);
		}
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
	private StringBuffer pointerValueToString(CIVLSource source, State state,
			SymbolicExpression pointer) {
		StringBuffer result = new StringBuffer();

		if (pointer.operator() == SymbolicOperator.NULL
				|| pointer.operator() != SymbolicOperator.TUPLE)
			result.append(pointer);
		else {
			SymbolicTupleType pointerType = (SymbolicTupleType) pointer.type();

			if (!pointerType.equals(this.pointerType)) {
				return this.symbolicExpressionToString(source, state, null,
						pointer, "", "");
			}
			return this.variableReferenceToString(state, source, false,
					this.symbolicUtil.getDyscopeId(source, pointer),
					symbolicUtil.getVariableId(source, pointer),
					symbolicUtil.getSymRef(pointer));
		}
		return result;
	}

	private StringBuffer variableReferenceToString(State state,
			CIVLSource source, boolean isMu, int dyscopeId, int vid,
			ReferenceExpression reference) {
		StringBuffer result = new StringBuffer();

		if (dyscopeId == -1 && vid == -1)
			result.append("NULL");
		if (dyscopeId < 0)
			result.append("UNDEFINED");
		else {
			DynamicScope dyscope = state.getDyscope(dyscopeId);
			Variable variable = dyscope.lexicalScope().variable(vid);

			if (variable.type().equals(this.heapType)) {
				result.append(heapObjectReferenceToString(source, dyscopeId,
						this.heapType, reference).third);
			} else {
				if (variable
						.name()
						.name()
						.startsWith(
								ModelConfiguration.ANONYMOUS_VARIABLE_PREFIX)) {
					SymbolicExpression stringExpression = state
							.getVariableValue(dyscopeId, vid);

					result.append("\"");
					result.append(this.symbolicUtil.charArrayToString(source,
							stringExpression, 0, true));
					result.append("\"");
				} else {
					if (!isMu)
						result.append('&');
					result.append("<");
					result.append("d" + dyscopeId);
					result.append('>');
					result.append(variable.name());
					result.append(referenceToString(source, variable.type(),
							reference).right);
				}
			}
		}
		return result;
	}

	private StringBuffer symbolicExpressionToString(CIVLSource source,
			State state, CIVLType type, SymbolicExpression symbolicExpression,
			String prefix, String separate) {
		return this.symbolicExpressionToString(source, state, type,
				symbolicExpression, false, prefix, separate);
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
	@SuppressWarnings("unchecked")
	private StringBuffer symbolicExpressionToString(CIVLSource source,
			State state, CIVLType civlType,
			SymbolicExpression symbolicExpression, boolean atomize,
			String prefix, String separator) {
		StringBuffer result = new StringBuffer();
		SymbolicType type = symbolicExpression.type();
		SymbolicType charType = typeFactory.charType().getDynamicType(universe);

		if (type == null)
			result.append("NULL");
		else if (type.equals(this.pointerType)) {
			// pointer
			return pointerValueToString(source, state, symbolicExpression);
		} else if (type.equals(this.functionPointerType)) {
			// function pointer
			return functionPointerValueToString(source, state,
					symbolicExpression);
		} else if (type.equals(this.dynamicHeapType)) {
			// heap
			return heapValueToString(source, state, symbolicExpression, prefix,
					separator);
		} else if (symbolicExpression.operator() == SymbolicOperator.ARRAY
				&& type instanceof SymbolicArrayType
				&& ((SymbolicArrayType) type).elementType().equals(charType)) {
			// string literal
			result.append("\"");
			result.append(this.symbolicUtil.charArrayToString(source,
					symbolicExpression, 0, true));
			result.append("\"");
		} else if (type.equals(procType)) {
			// $proc's
			if (symbolicExpression.operator() != SymbolicOperator.TUPLE)
				result.append(symbolicExpression);
			else {
				int pid = modelFactory.getProcessId(source, symbolicExpression);

				if (!modelFactory.isPocessIdDefined(pid)) {
					result.append("UNDEFINED");
				} else {
					if (pid < 0)
						result.append("$proc_null");
					else {
						ProcessState procState = state.getProcessState(pid);

						if (procState == null)
							result.append("UNDEFINED");
						else
							result.append(procState.name());
					}
				}
			}
		} else if (type.equals(scopeType)) {
			// $scope's
			if (symbolicExpression.operator() != SymbolicOperator.TUPLE)
				result.append(symbolicExpression);
			else {
				int scopeId = modelFactory.getScopeId(source,
						symbolicExpression);

				if (!modelFactory.isScopeIdDefined(scopeId))
					result.append("UNDEFINED");
				else
					result.append("d" + scopeId);
			}
		} else {
			SymbolicOperator operator = symbolicExpression.operator();

			// The structure of a symbolic expression has changed.
			// Symbolic collections are no longer used as arguments.
			// This code must be updated accordingly.
			if (operator == SymbolicOperator.TUPLE) {
				if (type.toString().equals("$domain")) {
					SymbolicExpression dimension = (SymbolicExpression) symbolicExpression
							.argument(0);
					String unionKind = symbolicExpression.argument(1)
							.toStringBuffer(false).toString();
					SymbolicExpression value = (SymbolicExpression) symbolicExpression
							.argument(2);

					if (unionKind.equals("0")) {
						result.append("($domain(");
						result.append(dimension.toStringBuffer(false));
						result.append("))");
					}
					result.append(this.symbolicExpressionToString(source,
							state, null, value, false, "", ""));
				} else if (type.toString().equals("$regular_range")) {
					int numArgs = symbolicExpression.numArguments();

					result.append("(");
					for (int i = 0; i < numArgs; i++) {
						if (i == 1)
							result.append("..");
						else if (i == 2) {
							result.append("#");
						}
						result.append(this.symbolicExpressionToString(source,
								state, null,
								(SymbolicExpression) symbolicExpression
										.argument(i), prefix, separator));
					}
					result.append(")");
				} else {
					result.append(symbolicTupleOrArrayToString(source, state,
							symbolicExpression, civlType, separator, prefix));
				}
				return result;
			} else if (operator == SymbolicOperator.ARRAY) {
				result.append(symbolicTupleOrArrayToString(source, state,
						symbolicExpression, civlType, separator, prefix));
				return result;
			} else if (operator == SymbolicOperator.CONCRETE) {
				SymbolicTypeKind tk = type.typeKind();

				// if (showType
				// && (type instanceof SymbolicArrayType || type instanceof
				// SymbolicTupleType)) {
				// result.append('(');
				// result.append(type.toStringBuffer(false));
				// result.append(')');
				// }
				if (tk == SymbolicTypeKind.CHAR) {
					result.append("'");
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(false));
					result.append("'");
				} else {
					if (symbolicExpression.type().equals(
							symbolicUtil.dynamicType())) {
						result.append(this.symbolicUtil
								.getStaticTypeOfDynamicType(symbolicExpression)
								.toString());
					} else {
						SymbolicObjectKind objectKind = symbolicExpression
								.argument(0).symbolicObjectKind();

						if (objectKind == SymbolicObjectKind.SEQUENCE) {
							result.append(symbolicSequenceToString(
									source,
									state,
									(SymbolicSequence<? extends SymbolicExpression>) symbolicExpression
											.argument(0), civlType, separator,
									prefix));
						} else {
							result.append(symbolicExpression.argument(0)
									.toStringBuffer(true));
						}
						if (type.isHerbrand())
							result.append('h');
					}
				}
				return result;
			} else {
				// if (showType
				// && (type instanceof SymbolicArrayType || type instanceof
				// SymbolicTupleType)) {
				// // if (tk == SymbolicTypeKind.TUPLE)
				// // result.append(type.toStringBuffer(false));
				// // else {
				// result.append('(');
				// result.append(type.toStringBuffer(false));
				// result.append(')');
				// // }
				// }
				switch (operator) {
				case ADD:
					processFlexibleBinaryNew(source, state, symbolicExpression,
							result, "+", false, atomize);
					break;
				case AND:
					processFlexibleBinaryNew(source, state, symbolicExpression,
							result, "&&", true, atomize);
					break;
				case APPLY: {
					String function = symbolicExpression.argument(0)
							.toStringBuffer(true).toString();

					result.append(function);
					result.append("(");
					accumulate(source, state, result, ",",
							(SymbolicSequence<?>) symbolicExpression
									.argument(1));
					result.append(")");
					break;
				}
				case ARRAY_LAMBDA:
					result.append("(" + symbolicExpression.argument(0) + ")");
					break;
				// return
				// symbolicExpression.toStringBufferLong().toString();
				case ARRAY_READ: {
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(true));
					result.append("[");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(false));
					result.append("]");
					break;
				}
				case ARRAY_WRITE: {
					boolean needNewLine = !civlType.areSubtypesScalar()
							&& !separator.isEmpty();
					String padding = "\n" + prefix + separator;
					String newPrefix = needNewLine ? prefix + separator
							: prefix;

					if (symbolicExpression.argument(0) instanceof SymbolicExpression) {
						result.append("(");
						result.append(this.symbolicExpressionToString(source,
								state, civlType,
								(SymbolicExpression) symbolicExpression
										.argument(0), false, prefix, separator));
						result.append(")");
					} else
						result.append(symbolicExpression.argument(0)
								.toStringBuffer(true));
					result.append("{");
					if (needNewLine)
						result.append(padding);
					result.append("[");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(false));
					result.append("]=");
					result.append(this.symbolicExpressionToString(
							source,
							state,
							((CIVLArrayType) civlType).elementType(),
							(SymbolicExpression) symbolicExpression.argument(2),
							true, newPrefix, separator));
					result.append("}");
					break;
				}
				case CAST:
					result.append('(');
					result.append(type.toStringBuffer(false));
					result.append(')');
					result.append(this
							.symbolicExpressionToString(source, state, null,
									(SymbolicExpression) symbolicExpression
											.argument(0), true, "", ""));
					break;
				case COND:
					result.append(this.symbolicExpressionToString(
							source,
							state,
							this.typeFactory.booleanType(),
							(SymbolicExpression) symbolicExpression.argument(0),
							true, "", ""));
					result.append(" ? ");
					result.append(this
							.symbolicExpressionToString(source, state,
									civlType,
									(SymbolicExpression) symbolicExpression
											.argument(1), true, "", ""));
					result.append(" : ");
					result.append(this
							.symbolicExpressionToString(source, state,
									civlType,
									(SymbolicExpression) symbolicExpression
											.argument(2), true, "", ""));
					if (atomize)
						atomize(result);
					break;
				case DENSE_ARRAY_WRITE: {
					int count = 0;
					boolean first = true;
					boolean needNewLine = !separator.isEmpty()
							&& civlType != null ? !civlType.areSubtypesScalar()
							: false;
					String padding = "\n" + prefix + separator;
					String newPrefix = needNewLine ? prefix + separator
							: prefix;

					if (symbolicExpression.argument(0) instanceof SymbolicExpression) {
						result.append("(");
						result.append(this.symbolicExpressionToString(source,
								state, civlType,
								(SymbolicExpression) symbolicExpression
										.argument(0), atomize, prefix,
								separator));
						result.append(")");
					} else
						result.append(symbolicExpression.argument(0)
								.toStringBuffer(true));
					result.append("{");
					for (SymbolicExpression value : (SymbolicSequence<?>) symbolicExpression
							.argument(1)) {
						if (!value.isNull()) {
							if (first)
								first = false;
							else
								result.append(", ");
							if (needNewLine)
								result.append(padding);
							result.append("[" + count + "]" + "=");
							result.append(symbolicExpressionToString(source,
									state, this.subType(civlType, count).right,
									value, false, newPrefix, separator));
							// result.append(value.toStringBuffer(false));
						}
						count++;
					}
					result.append("}");
					break;
				}
				case DENSE_TUPLE_WRITE: {
					boolean first = true;
					int eleIndex = 0;
					boolean allSubtypesScalar = civlType.areSubtypesScalar();
					boolean needNewLine = !separator.isEmpty()
							&& !allSubtypesScalar;
					String padding = "\n" + prefix + separator;
					String newPrefix = needNewLine ? prefix + separator
							: prefix;
					SymbolicSequence<?> elements = (SymbolicSequence<?>) symbolicExpression
							.argument(1);
					boolean needBrackets = allSubtypesScalar
							|| elements.size() == 0;

					result.append(symbolicExpression.argument(0)
							.toStringBuffer(true));
					if (needBrackets)
						result.append("{");
					for (SymbolicExpression value : elements) {
						if (!value.isNull()) {
							Pair<String, CIVLType> eleNameAndType = this
									.subType(civlType, eleIndex);

							if (first)
								first = false;
							else
								result.append(", ");
							if (needNewLine)
								result.append(padding);
							result.append("." + eleNameAndType.left + "=");
							result.append(symbolicExpressionToString(source,
									state, eleNameAndType.right, value, false,
									newPrefix, separator));
						}
						eleIndex++;
					}
					if (needBrackets)
						result.append("}");
					break;
				}
				case DIVIDE:
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(true));
					result.append("/");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(true));
					if (atomize)
						atomize(result);
					break;
				case EQUALS:
					processFlexibleBinary(source, state, symbolicExpression,
							result, "==", true, atomize);
					break; // if (arguments[0] instanceof SymbolicExpression)
				// result.append(this.symbolicExpressionToString(source,
				// state, null, (SymbolicExpression) arguments[0]));
				// else
				// result.append(arguments[0].toStringBuffer(false));
				// result.append("==");
				// if (arguments[1] instanceof SymbolicExpression)
				// result.append(this.symbolicExpressionToString(source,
				// state, null, (SymbolicExpression) arguments[1]));
				// else
				// result.append(arguments[1].toStringBuffer(false));
				// if (atomize)
				// atomize(result);
				// return result.toString();
				case EXISTS:
					result.append("exists ");
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(false));
					result.append(" : ");
					result.append(((SymbolicExpression) symbolicExpression
							.argument(0)).type().toStringBuffer(false));
					result.append(" . ");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(true));
					if (atomize)
						atomize(result);
					break;
				case FORALL:
					result.append("forall ");
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(false));
					result.append(" : ");
					result.append(((SymbolicExpression) symbolicExpression
							.argument(0)).type().toStringBuffer(false));
					result.append(" . ");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(true));
					if (atomize)
						atomize(result);
					break;
				case INT_DIVIDE: {
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(true));
					// result.append("\u00F7");
					result.append("/");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(true));
					if (atomize)
						atomize(result);
					break;
				}
				case LAMBDA:
					result.append("lambda ");
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(false));
					result.append(" : ");
					result.append(((SymbolicExpression) symbolicExpression
							.argument(0)).type().toStringBuffer(false));
					result.append(" . ");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(true));
					if (atomize)
						atomize(result);
					break;
				case LENGTH:
					result.append("length(");
					result.append(this
							.symbolicExpressionToString(source, state, null,
									(SymbolicExpression) symbolicExpression
											.argument(0), "", ""));
					result.append(")");
					break;
				case LESS_THAN:
					processFlexibleBinaryNew(source, state, symbolicExpression,
							result, "<", true, atomize);
					break;
				case LESS_THAN_EQUALS:
					processFlexibleBinaryNew(source, state, symbolicExpression,
							result, "<=", true, atomize);
					break;
				case MODULO:
					processFlexibleBinary(source, state, symbolicExpression,
							result, "%", true, atomize);
					break;
				case MULTIPLY:
					processFlexibleBinaryNew(source, state, symbolicExpression,
							result, "*", true, atomize);
					break;
				case NEGATIVE:
					result.append("-");
					result.append(this
							.symbolicExpressionToString(source, state, null,
									(SymbolicExpression) symbolicExpression
											.argument(0), "", ""));
					atomize(result);
					break;
				case NEQ:
					result.append(this
							.symbolicExpressionToString(source, state, null,
									(SymbolicExpression) symbolicExpression
											.argument(0), "", ""));
					result.append("!=");
					result.append(this
							.symbolicExpressionToString(source, state, null,
									(SymbolicExpression) symbolicExpression
											.argument(1), true, "", ""));
					if (atomize)
						atomize(result);
					break;
				case NOT:
					result.append("!");
					result.append(this
							.symbolicExpressionToString(source, state, null,
									(SymbolicExpression) symbolicExpression
											.argument(0), true, "", ""));
					if (atomize)
						atomize(result);
					break;
				case NULL:
					result.append("NULL");
					break;
				case OR:
					processFlexibleBinaryNew(source, state, symbolicExpression,
							result, "||", false, atomize);
					break;
				case POWER:
					processFlexibleBinary(source, state, symbolicExpression,
							result, "^", false, atomize);
					break;
				case SUBTRACT:
					processFlexibleBinary(source, state, symbolicExpression,
							result, "-", false, atomize);
					break;
				case SYMBOLIC_CONSTANT:
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(true));
					break;
				case TUPLE_READ:
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(true));
					result.append(".");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(false));
					if (atomize)
						atomize(result);
					break;
				case TUPLE_WRITE: {
					boolean needNewLine = !separator.isEmpty()
							&& !civlType.areSubtypesScalar();
					String padding = "\n" + prefix + separator;
					String newPrefix = needNewLine ? prefix + separator
							: prefix;
					int fieldIndex = ((IntObject) symbolicExpression
							.argument(1)).getInt();
					StructOrUnionField field = ((CIVLStructOrUnionType) civlType)
							.getField(fieldIndex);

					result.append(symbolicExpression.argument(0)
							.toStringBuffer(true));
					result.append("{");
					if (needNewLine)
						result.append(padding);
					result.append(".");
					result.append(field.name().name());
					result.append(":=");
					result.append(this.symbolicExpressionToString(source,
							state, field.type(), symbolicExpression, newPrefix,
							separator));
					result.append("}");
					break;
				}
				case UNION_EXTRACT:
					result.append("extract(");
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(false));
					result.append(",");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(false));
					result.append(")");
					break;
				case UNION_INJECT: {
					result.append(this
							.symbolicExpressionToString(source, state,
									civlType,
									(SymbolicExpression) symbolicExpression
											.argument(1), false, prefix,
									separator));
					break;
				}
				case UNION_TEST:
					result.append("test(");
					result.append(symbolicExpression.argument(0)
							.toStringBuffer(false));
					result.append(",");
					result.append(symbolicExpression.argument(1)
							.toStringBuffer(false));
					result.append(")");
					break;
				default:
					result.append(symbolicExpression.toStringBufferLong());
				}
			}
		}
		return result;
	}

	private StringBuffer symbolicTupleOrArrayToString(CIVLSource source,
			State state, SymbolicExpression tuppleOrArray, CIVLType civlType,
			String separator, String prefix) {
		StringBuffer result = new StringBuffer();
		// int elementIndex = 0;
		boolean allSubtypesScalar = civlType != null ? civlType
				.areSubtypesScalar() : false;
		boolean needNewLine = !separator.isEmpty() && !allSubtypesScalar;
		String padding = "\n" + prefix + separator;
		String newPrefix = needNewLine ? prefix + separator : prefix;
		int numArgs = tuppleOrArray.numArguments();
		boolean needBrackets = allSubtypesScalar || numArgs == 0;
		boolean isArray = civlType != null ? civlType.isArrayType() : false;

		if (needBrackets)
			result.append("{");
		for (int i = 0; i < numArgs; i++) {
			Pair<String, CIVLType> elementNameAndType = this.subType(civlType,
					i);
			CIVLType eleType = elementNameAndType.right;
			boolean subtypesOfEleScalar = eleType != null ? eleType
					.areSubtypesScalar() : false;
			boolean eleEmpty = false;
			SymbolicExpression symbolicElement = (SymbolicExpression) tuppleOrArray
					.argument(i);

			eleEmpty = symbolicElement.numArguments() == 0;
			if (i != 0 && !needNewLine)
				result.append(", ");
			if (needNewLine)
				result.append(padding);
			if (elementNameAndType.left != null)
				result.append("." + elementNameAndType.left);
			else if (isArray)
				result.append("[" + i + "]");
			if (subtypesOfEleScalar || eleEmpty)
				result.append("=");
			else if (eleType != null)
				result.append(": " + eleType);
			result.append(symbolicExpressionToString(source, state,
					elementNameAndType.right, symbolicElement, false,
					newPrefix, separator));
		}
		if (needBrackets)
			result.append("}");
		return result;
	}

	private StringBuffer symbolicSequenceToString(CIVLSource source,
			State state,
			SymbolicSequence<? extends SymbolicExpression> symbolicCollection,
			CIVLType civlType, String separator, String prefix) {
		StringBuffer result = new StringBuffer();
		int elementIndex = 0;
		boolean allSubtypesScalar = civlType != null ? civlType
				.areSubtypesScalar() : false;
		boolean needNewLine = !separator.isEmpty() && !allSubtypesScalar;
		String padding = "\n" + prefix + separator;
		String newPrefix = needNewLine ? prefix + separator : prefix;
		boolean needBrackets = allSubtypesScalar
				|| symbolicCollection.size() == 0;
		boolean isArray = civlType != null ? civlType.isArrayType() : false;

		if (needBrackets)
			result.append("{");
		for (SymbolicExpression symbolicElement : symbolicCollection) {
			Pair<String, CIVLType> elementNameAndType = this.subType(civlType,
					elementIndex);
			CIVLType eleType = elementNameAndType.right;
			boolean subtypesOfEleScalar = eleType != null ? eleType
					.areSubtypesScalar() : false;
			boolean eleEmpty = false;

			if (symbolicElement.argument(0) instanceof SymbolicSequence) {
				@SuppressWarnings("unchecked")
				SymbolicSequence<? extends SymbolicExpression> symbolicEleCollection = (SymbolicSequence<? extends SymbolicExpression>) symbolicElement
						.argument(0);

				eleEmpty = symbolicEleCollection.size() == 0;
			}
			if (elementIndex != 0 && !needNewLine)
				result.append(", ");
			if (needNewLine)
				result.append(padding);
			if (elementNameAndType.left != null)
				result.append("." + elementNameAndType.left);
			else if (isArray)
				result.append("[" + elementIndex + "]");
			if (subtypesOfEleScalar || eleEmpty)
				result.append("=");
			else if (eleType != null)
				result.append(": " + eleType);
			elementIndex++;
			result.append(symbolicExpressionToString(source, state,
					elementNameAndType.right, symbolicElement, false,
					newPrefix, separator));
		}
		if (needBrackets)
			result.append("}");
		return result;
	}

	/**
	 * Returns the i-th sub-type (and its name if it is a struct or union field)
	 * of the given type. If the given type is an array type, then return the
	 * element type; if the given type is a struct or union type, then returns
	 * the i-th field type. Returns null for other types.
	 * 
	 * @param type
	 * @param i
	 * @return
	 */
	private Pair<String, CIVLType> subType(CIVLType type, int i) {
		if (type != null)
			if (type instanceof CIVLArrayType) {
				CIVLArrayType arrayType = (CIVLArrayType) type;

				return new Pair<>(null, arrayType.elementType());
			} else if (type instanceof CIVLStructOrUnionType) {
				CIVLStructOrUnionType structOrUnionType = (CIVLStructOrUnionType) type;

				if (structOrUnionType.numFields() > 0) {
					StructOrUnionField field = structOrUnionType.getField(i);

					return new Pair<>(field.name().name(), field.type());
				}
			}
		return new Pair<>(null, null);
	}

	/**
	 * Constructs the pretty presentation of a heap.
	 * 
	 * For example:
	 * 
	 * <pre>
	 * | | | | __heap = 
	 * | | | | | objects of malloc 0 by f0:14.2-53 "p1d = (double *) ... )":
	 * | | | | | | 0: H0[0:=0]
	 * | | | | | objects of malloc 1 by f0:15.2-56 "p2d = (double ** ... )":
	 * | | | | | | 0: H1[0:=&<d0>heap<3,0>[0]]
	 * | | | | | objects of malloc 2 by f0:16.2-58 "p3d = (double ** ... )":
	 * | | | | | | 0: H2[0:=&<d0>heap<4,0>[0]]
	 * | | | | | objects of malloc 3 by f0:19.4-58 "p2d[i] = (double ... )":
	 * | | | | | | 0: H3[0:=0, 1:=1, 2:=2]
	 * | | | | | objects of malloc 4 by f0:20.4-61 "p3d[i] = (double ... )":
	 * | | | | | | 0: H4[0:=&<d0>heap<5,0>[0], 1:=&<d0>heap<5,1>[0], 2:=&<d0>heap<5,2>[0]]
	 * | | | | | objects of malloc 5 by f0:23.6-63 "p3d[i][j] = ... )":
	 * | | | | | | 0: H5[0:=0, 1:=1, 2:=2, 3:=3, 4:=4, 5:=5, 6:=6, 7:=7, 8:=8, 9:=9]
	 * | | | | | | 1: H6[0:=10, 1:=11, 2:=12, 3:=13, 4:=14, 5:=15, 6:=16, 7:=17, 8:=18, 9:=19]
	 * | | | | | | 2: H7[0:=20, 1:=21, 2:=22, 3:=23, 4:=24, 5:=25, 6:=26, 7:=27]
	 * </pre>
	 * 
	 * @param source
	 *            The source code element for error report.
	 * @param state
	 *            The current state.
	 * @param heapValue
	 *            The value of the heap to be printed.
	 * @param prefix
	 *            The prefix of the heap value in printing.
	 * @param separate
	 *            The separate string for sub-components of the heap.
	 * @return The pretty presentation of a heap for printing.
	 */
	private StringBuffer heapValueToString(CIVLSource source, State state,
			SymbolicExpression heapValue, String prefix, String separate) {
		StringBuffer result = new StringBuffer();
		int numFields = typeFactory.heapType().getNumMallocs();
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		String fieldPrefix = prefix + separate;
		String objectPrefix = fieldPrefix + separate;

		if (heapValue.isNull()) {
			result.append("NULL");
		}
		for (int i = 0; i < numFields; i++) {
			SymbolicExpression heapField = universe.tupleRead(heapValue,
					universe.intObject(i));
			NumericExpression fieldLength = universe.length(heapField);
			int length;
			CIVLSource mallocSource;
			CIVLType fieldTypeElement = heapType.getMalloc(i)
					.getStaticElementType();

			if (fieldLength.isZero())
				continue;
			result.append("\n");
			result.append(fieldPrefix);

			result.append("objects of malloc ");
			result.append(i);
			mallocSource = this.heapType.getMalloc(i).getSource();
			if (mallocSource != null) {
				result.append(" at ");
				result.append(mallocSource.getSummary());
			}
			// result.append(":");
			length = ((IntegerNumber) reasoner.extractNumber(fieldLength))
					.intValue();
			for (int j = 0; j < length; j++) {
				SymbolicExpression heapObject = universe.arrayRead(heapField,
						universe.integer(j));
				IntegerNumber heapObjLenNumber = ((IntegerNumber) reasoner
						.extractNumber(universe.length(heapObject)));
				CIVLType heapObjType = null;

				if (heapObjLenNumber != null) {
					int heapObjSize = ((IntegerNumber) reasoner
							.extractNumber(universe.length(heapObject)))
							.intValue();

					heapObjType = this.typeFactory.completeArrayType(
							fieldTypeElement, this.modelFactory
									.integerLiteralExpression(mallocSource,
											BigInteger.valueOf(heapObjSize)));
				} else
					heapObjType = this.typeFactory
							.incompleteArrayType(fieldTypeElement);
				result.append("\n");
				result.append(objectPrefix);
				result.append(j);
				result.append(": ");
				result.append(heapObjType);
				result.append(this.symbolicExpressionToString(source, state,
						heapObjType, heapObject, false, objectPrefix, separate));
			}
		}
		if (result.length() == 0)
			result.append("EMPTYP");
		return result;
	}

	private CIVLType typeOfObjByRef(CIVLType type, ReferenceExpression ref) {
		if (ref.isIdentityReference())
			return type;
		else if (ref.isArrayElementReference()) {
			ArrayElementReference arrayEleRef = (ArrayElementReference) ref;
			CIVLType parentType = typeOfObjByRef(type, arrayEleRef.getParent());

			if (parentType.isDomainType())
				return typeFactory.rangeType();
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
				CIVLArrayType heapTupleType = typeFactory
						.incompleteArrayType(((CIVLHeapType) parentType)
								.getMalloc(index).getStaticElementType());

				heapTupleType = typeFactory.incompleteArrayType(heapTupleType);
				return heapTupleType;
			}
			return ((CIVLStructOrUnionType) parentType).getField(index).type();
		}
	}

	@Override
	public Pair<State, String> expressionEvaluation(State state, int pid,
			Expression expression, boolean resultOnly)
			throws UnsatisfiablePathConditionException {
		return this.expressionEvaluationWorker(state, pid, expression,
				resultOnly, true);
	}

	private Pair<State, String> expressionEvaluation(State state, int pid,
			Expression expression) throws UnsatisfiablePathConditionException {
		return this.expressionEvaluation(state, pid, expression, false);
	}

	private Pair<State, String> expressionEvaluationFinalResult(State state,
			int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		return this.expressionEvaluationWorker(state, pid, expression, true,
				false);
	}

	private StringBuffer evaluateLHSExpression(State state, int pid,
			LHSExpression lhs) throws UnsatisfiablePathConditionException {
		LHSExpressionKind kind = lhs.lhsExpressionKind();
		StringBuffer result = new StringBuffer();

		switch (kind) {
		case DEREFERENCE: {
			result.append("*(");
			result.append(this.expressionEvaluation(state, pid,
					((DereferenceExpression) lhs).pointer()).right);
			result.append(")");
			break;
		}
		case DOT: {
			DotExpression dot = (DotExpression) lhs;
			Expression structOrUnion = dot.structOrUnion();

			result.append("(");
			if (structOrUnion instanceof LHSExpression)
				result.append(this.evaluateLHSExpression(state, pid,
						(LHSExpression) structOrUnion));
			else
				result.append(this.expressionEvaluation(state, pid,
						structOrUnion).right);
			result.append(").");
			assert structOrUnion.getExpressionType() instanceof CIVLStructOrUnionType;
			result.append(((CIVLStructOrUnionType) structOrUnion
					.getExpressionType()).getField(dot.fieldIndex()).name()
					.name());
			break;
		}
		case SUBSCRIPT: {
			SubscriptExpression subscript = (SubscriptExpression) lhs;

			result.append(this.evaluateLHSExpression(state, pid,
					subscript.array()));
			result.append("[");
			result.append(this.expressionEvaluationFinalResult(state, pid,
					subscript.index()).right);
			result.append("]");
			break;
		}
		case VARIABLE:
			result.append(((VariableExpression) lhs).variable().name().name());
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"evaluating left-hand-side expression of " + kind + " kind",
					lhs.getSource());
		}
		return result;
	}

	@Override
	public StringBuffer statementEvaluation(State state, State postState,
			int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		StatementKind kind = statement.statementKind();
		StringBuffer result = new StringBuffer();
		Pair<State, String> tmp;

		switch (kind) {
		case ASSIGN: {
			if (statement instanceof AtomicLockAssignStatement) {
				AtomicLockAssignStatement atomicLockStmt = (AtomicLockAssignStatement) statement;
				String process = state.getProcessState(pid).name();
				int previousAtomicCount = state.getProcessState(pid)
						.atomicCount();

				if (atomicLockStmt.enterAtomic()) {
					result.append("ENTER_ATOMIC [");
					if (previousAtomicCount < 1)
						result.append(ModelConfiguration.ATOMIC_LOCK_VARIABLE
								+ ":=" + process + ", ");
					result.append(process + ".atomicCount:="
							+ (previousAtomicCount + 1));
					result.append("]");
				} else {
					result.append("LEAVE_ATOMIC [");

					if (previousAtomicCount == 1)
						result.append(ModelConfiguration.ATOMIC_LOCK_VARIABLE
								+ ":=$proc_null, ");
					result.append(process + ".atomicCount:=0");
					result.append("]");
				}
			} else {
				AssignStatement assign = (AssignStatement) statement;
				LHSExpression lhs = assign.getLhs();
				Expression rhs = assign.rhs();
				StringBuffer lhsString = this.evaluateLHSExpression(state, pid,
						lhs);
				String rhsString = this.expressionEvaluation(state, pid, rhs).right
						.toString();
				String newRhsString = this.expressionEvaluationFinalResult(
						state, pid, rhs).right;

				result.append(lhsString);
				result.append("=");
				result.append(rhsString);
				if (!rhsString.equals(newRhsString)) {
					result.append(" ");
					result.append(SEF_START);
					result.append(lhsString);
					result.append(SEF);
					result.append(newRhsString);
					result.append(SEF_END);
				}
			}
			break;
		}
		case CALL_OR_SPAWN: {
			CallOrSpawnStatement callOrSpawn = (CallOrSpawnStatement) statement;
			CIVLFunction function = callOrSpawn.function();
			List<Expression> args = callOrSpawn.arguments();
			int numArgs = args.size();
			LHSExpression lhs = callOrSpawn.lhs();
			StringBuffer lhsString = null;

			if (lhs != null) {
				lhsString = this.evaluateLHSExpression(state, pid, lhs);
				result.append(lhsString);
				result.append("=");
			}
			if (callOrSpawn.isSpawn())
				result.append("$spawn ");
			if (function == null) {
				function = this.evaluator.evaluateFunctionIdentifier(state,
						pid, callOrSpawn.functionExpression(),
						callOrSpawn.getSource()).second;
				assert function != null;
			}
			result.append(function.name().name());
			result.append("(");
			for (int i = 0; i < numArgs; i++) {
				Expression arg = args.get(i);

				if (i != 0)
					result.append(", ");
				tmp = this.expressionEvaluation(state, pid, arg);
				result.append(tmp.right);
			}
			result.append(")");
			if (lhs != null
					&& (callOrSpawn.isSpawn() || callOrSpawn.isSystemCall())) {
				String newLhsValue = this.expressionEvaluationFinalResult(
						postState, pid, lhs).right;

				if (newLhsValue != null) {
					result.append(" ");
					result.append(SEF_START);
					result.append(lhsString);
					result.append(SEF);
					result.append(this.expressionEvaluationFinalResult(
							postState, pid, lhs).right);
					result.append(SEF_END);
				}
			}
			break;
		}
		case DOMAIN_ITERATOR: {
			DomainIteratorStatement civlForEnter = (DomainIteratorStatement) statement;
			List<Variable> loopVars = civlForEnter.loopVariables();
			int dim = loopVars.size();

			result.append("NEXT of (");
			for (int i = 0; i < dim; i++) {
				Variable loopVar = loopVars.get(i);

				if (i != 0)
					result.append(", ");
				result.append(this.symbolicExpressionToString(
						loopVar.getSource(), state, loopVar.type(),
						state.valueOf(pid, loopVar), "", ""));
			}
			result.append(") in ");
			tmp = this.expressionEvaluation(state, pid, civlForEnter.domain());
			result.append(tmp.right);
			result.append(" [");
			for (int i = 0; i < dim; i++) {
				Variable loopVar = loopVars.get(i);

				if (i != 0)
					result.append(", ");
				result.append(loopVar.name().name());
				result.append(":=");
				result.append(this.symbolicExpressionToString(
						loopVar.getSource(), postState, loopVar.type(),
						postState.valueOf(pid, loopVar), "", ""));
			}
			result.append("]");
			break;
		}
		case CIVL_PAR_FOR_ENTER: {
			// $parfor(i0, i1, i2: dom) $spawn function(i0, i1, i2);
			CivlParForSpawnStatement parForEnter = (CivlParForSpawnStatement) statement;
			StringBuffer arguments = new StringBuffer();

			for (int i = 0; i < parForEnter.dimension(); i++) {
				if (i != 0)
					arguments.append(",");
				arguments.append("i");
				arguments.append(i);
			}
			result.append("$parfor(");
			result.append(arguments);
			result.append(": ");
			result.append(this.expressionEvaluation(state, pid,
					parForEnter.domain()).right);
			result.append(")");
			result.append(" $spawn ");
			result.append(parForEnter.parProcFunction().name().name());
			result.append("(");
			result.append(arguments);
			result.append(")");
			break;
		}
		case MALLOC: {
			MallocStatement malloc = (MallocStatement) statement;
			LHSExpression lhs = malloc.getLHS();
			StringBuffer lhsString = null;
			String newLhsString;

			if (lhs != null) {
				lhsString = this.evaluateLHSExpression(state, pid, lhs);
				result.append(lhsString);
				result.append("=");
			}
			result.append("(");
			result.append(malloc.getStaticElementType());
			result.append("*)");
			result.append("$malloc(");
			result.append(this.expressionEvaluation(state, pid,
					malloc.getScopeExpression()).right);
			result.append(", ");
			result.append(this.expressionEvaluation(state, pid,
					malloc.getSizeExpression()).right);
			result.append(") ");
			newLhsString = this.expressionEvaluationFinalResult(postState, pid,
					lhs).right;
			if (newLhsString != null) {
				result.append(SEF_START);
				result.append(lhsString);
				result.append(SEF);
				result.append(newLhsString);
				result.append(SEF_END);
			}
			break;
		}
		case NOOP: {
			Expression guard = statement.guard();

			result.append(statement.toString());
			result.append(" (guard: ");
			result.append(this.expressionEvaluation(state, pid, guard, false).right);
			result.append(")");
			break;
		}
		case RETURN: {
			// return expression (assigning to...)
			// ProcessState procState=state.getProcessState(pid);
			CIVLFunction function = state.getProcessState(pid).peekStack()
					.location().function();
			// String functionName;
			Expression expression = ((ReturnStatement) statement).expression();
			StackEntry callerStack = state.getProcessState(pid)
					.peekSecondLastStack();
			CallOrSpawnStatement caller = null;

			if (callerStack != null)
				caller = (CallOrSpawnStatement) callerStack.location()
						.getSoleOutgoing();
			assert function != null;
			result.append(function.name().name());
			result.append("(...) return");
			if (expression != null) {
				result.append(" ");
				result.append(this.expressionEvaluation(state, pid, expression).right);
				if (caller != null) {
					LHSExpression lhs = caller.lhs();

					if (lhs != null) {
						result.append(" ");
						result.append(SEF_START);
						result.append(this.evaluateLHSExpression(state, pid,
								lhs));
						result.append(SEF);
						result.append(this.expressionEvaluationFinalResult(
								state, pid, expression).right);
						result.append(SEF_END);
					}
				}
			}
			break;
		}
		default:
			throw new CIVLUnimplementedFeatureException(
					"evaluating statement of " + kind + " kind",
					statement.getSource());
		}
		return result;

	}

	private Pair<State, String> expressionEvaluationWorker(State state,
			int pid, Expression expression, boolean resultOnly,
			boolean isTopLevel) throws UnsatisfiablePathConditionException {
		ExpressionKind kind = expression.expressionKind();
		StringBuilder result = new StringBuilder();
		Pair<State, String> temp;
		CIVLType exprType = expression.getExpressionType();

		if (resultOnly && !isTopLevel) {
			Evaluation eval;

			try {
				eval = this.evaluator.evaluate(state, pid, expression);
			} catch (Exception ex) {
				return new Pair<>(state, (String) null);
			}
			state = eval.state;
			result.append(this.symbolicExpressionToString(
					expression.getSource(), state, exprType, eval.value,
					!isTopLevel, "", ""));
		} else {
			switch (kind) {
			case ABSTRACT_FUNCTION_CALL: {
				AbstractFunctionCallExpression abstractFuncCall = (AbstractFunctionCallExpression) expression;
				int i = 0;
				result.append(abstractFuncCall.function().name().name());
				result.append("(");
				for (Expression argument : abstractFuncCall.arguments()) {
					if (i != 0)
						result.append(", ");
					i++;
					temp = expressionEvaluationWorker(state, pid, argument,
							resultOnly, false);
					result.append(temp.right);
					state = temp.left;
				}
				result.append(")");
				break;
			}
			case BINARY: {
				BinaryExpression binary = (BinaryExpression) expression;

				if (!isTopLevel)
					result.append("(");
				temp = this.expressionEvaluationWorker(state, pid,
						binary.left(), resultOnly, false);
				state = temp.left;
				result.append(temp.right);
				result.append(binary.operatorToString());
				temp = this.expressionEvaluationWorker(state, pid,
						binary.right(), resultOnly, false);
				state = temp.left;
				result.append(temp.right);
				if (!isTopLevel)
					result.append(")");
				break;
			}
			case CAST: {
				CastExpression cast = (CastExpression) expression;

				result.append("(");
				result.append(cast.getCastType().toString());
				result.append(")");
				temp = this.expressionEvaluationWorker(state, pid,
						cast.getExpression(), resultOnly, false);
				state = temp.left;
				result.append(temp.right);
				break;
			}
			case COND: {
				throw new CIVLInternalException(
						"Conditional expression is unreachable because it should"
								+ " have been traslated away by the model builder.",
						expression.getSource());
			}
			case DEREFERENCE: {
				DereferenceExpression dereference = (DereferenceExpression) expression;

				result.append("*");
				temp = this.expressionEvaluationWorker(state, pid,
						dereference.pointer(), resultOnly, false);
				state = temp.left;
				result.append(temp.right);
				break;
			}
			case DOMAIN_GUARD: {
				DomainGuardExpression domGuard = (DomainGuardExpression) expression;
				int dim = domGuard.dimension();

				temp = this.expressionEvaluationWorker(state, pid,
						domGuard.domain(), resultOnly, false);
				state = temp.left;
				result.append(temp.right);
				result.append(" has next for (");
				for (int i = 0; i < dim; i++) {
					Variable var = domGuard.variableAt(i);

					if (i != 0)
						result.append(", ");
					result.append(this.symbolicExpressionToString(
							var.getSource(),
							state,
							var.type(),
							state.getVariableValue(
									state.getDyscope(pid, var.scope()),
									var.vid())));
				}
				result.append(")");
				break;
			}
			case FUNCTION_IDENTIFIER: {
				FunctionIdentifierExpression functionID = (FunctionIdentifierExpression) expression;
				Triple<State, CIVLFunction, Integer> functionResult = this.evaluator
						.evaluateFunctionIdentifier(state, pid, functionID,
								expression.getSource());

				state = functionResult.first;
				result.append(functionResult.second.name().name());
				break;
			}
			case QUANTIFIER: {
				result.append(expression.toString());
				break;
			}
			case UNARY: {
				UnaryExpression unary = (UnaryExpression) expression;

				result.append(unary.operatorToString());
				temp = this.expressionEvaluationWorker(state, pid,
						unary.operand(), resultOnly, false);
				state = temp.left;
				result.append(temp.right);
				break;
			}
			case INITIAL_VALUE: {
				result.append(expression.toString());
				break;
			}
			case ADDRESS_OF:
			case ARRAY_LITERAL:
			case BOOLEAN_LITERAL:
			case CHAR_LITERAL:
			case DOT:
			case DYNAMIC_TYPE_OF:
			case HERE_OR_ROOT:
			case INTEGER_LITERAL:
			case MEMORY_UNIT:
			case NULL_LITERAL:
			case REAL_LITERAL:
			case REGULAR_RANGE:
			case SIZEOF_TYPE:
			case SIZEOF_EXPRESSION:
			case STRING_LITERAL:
			case STRUCT_OR_UNION_LITERAL:
			case SUBSCRIPT:
			case VARIABLE:
			case REC_DOMAIN_LITERAL: {
				Evaluation eval = this.evaluator.evaluate(state, pid,
						expression);

				state = eval.state;
				result.append(this.symbolicExpressionToString(
						expression.getSource(), state, exprType, eval.value,
						"", ""));
				break;
			}
			case BOUND_VARIABLE:
			case DERIVATIVE:
			case FUNCTION_GUARD:
			case RESULT:
			case SCOPEOF:
			case SELF:
			case SYSTEM_GUARD:
			case UNDEFINED_PROC:
			case PROC_NULL: {
				result.append(expression.toString());
				break;
			}
			default:
				throw new CIVLUnimplementedFeatureException(
						"printing the evaluation of expression of " + kind
								+ " kind", expression.getSource());
			}
		}
		return new Pair<>(state, result.toString());
	}

	void setEvaluator(Evaluator evaluator) {
		this.evaluator = evaluator;
	}

	@Override
	public StringBuffer stateInformation(State state) {
		StringBuffer result = new StringBuffer();

		result.append(this.inputVariablesToStringBuffer(state));
		result.append("\nContext:");
		result.append(this.pathconditionToString(null, state, "  ",
				state.getPathCondition()));
		result.append(state.callStackToString());
		return result;
	}

	@Override
	public StringBuffer inputVariablesToStringBuffer(State state) {
		Map<Variable, SymbolicExpression> inputVariableValues = evaluator
				.stateFactory().inputVariableValueMap(state);
		StringBuffer result = new StringBuffer("");

		if (!inputVariableValues.isEmpty())
			result.append("\nInput:");
		for (Map.Entry<Variable, SymbolicExpression> entry : inputVariableValues
				.entrySet()) {
			result.append("\n  ");
			result.append(entry.getKey().name().name());
			result.append("=");
			result.append(this.symbolicExpressionToString(entry.getKey()
					.getSource(), state, entry.getKey().type(), entry
					.getValue(), "", ""));
		}
		return result;
	}

	@Override
	public Evaluator evaluator() {
		return this.evaluator;
	}

	/**
	 * C11, 6.2.6.1 paragraph 4:
	 * 
	 * Values stored in non-bit-field objects of any other object type consist
	 * of n × CHAR_BIT bits, where n is the size of an object of that type, in
	 * bytes. The value may be copied into an object of type unsigned char [ n ]
	 * (e.g., by memcpy); the resulting set of bytes is called the object
	 * representation of the value.
	 * 
	 * 6.3.2.3 Pointers p7:
	 * 
	 * ... When a pointer to an object is converted to a pointer to a character
	 * type, the result points to the lowest addressed byte of the object.
	 * Successive increments of the result, up to the size of the object, yield
	 * pointers to the remaining bytes of the object.
	 * 
	 * @param source
	 * @param state
	 * @param isSubtract
	 * @param pointer
	 * @param offset
	 * @return
	 */
	@Override
	public SymbolicExpression pointerArithmetics(CIVLSource source,
			State state, boolean isSubtract, SymbolicExpression pointer,
			SymbolicExpression offset) {
		SymbolicExpression result = null;

		if (isSubtract) {
			assert this.symbolicUtil.getDyscopeId(source, offset) == -1;
			assert this.symbolicUtil.getVariableId(source, offset) == -1;

			ReferenceExpression offsetRef = symbolicUtil.getSymRef(offset);
			return symbolicUtil.setSymRef(pointer,
					this.subtract(symbolicUtil.getSymRef(pointer), offsetRef));
		}
		return result;
	}

	/**
	 * left-right
	 * 
	 * for example, if left is TupleComponenent(<Ref 1>, 1), and right is
	 * TupleComponent(<Ref 1>, 1), then result is <Ref 1>.
	 * 
	 * @param left
	 * @param right
	 * @return
	 */
	private ReferenceExpression subtract(ReferenceExpression left,
			ReferenceExpression right) {
		if (universe.equals(left, right).isTrue())
			return universe.identityReference();
		return null;
	}

	@Override
	public Pair<BooleanExpression, ResultType> isDerefablePointer(State state,
			SymbolicExpression pointer) {
		if (this.symbolicUtil.isNullPointer(pointer) || pointer.isNull())
			return new Pair<>(universe.falseExpression(), ResultType.NO);

		int dyscope = symbolicUtil.getDyscopeId(null, pointer);

		if (dyscope < 0)
			return new Pair<>(universe.falseExpression(), ResultType.NO);

		int vid = symbolicUtil.getVariableId(null, pointer);
		SymbolicExpression value = state.getVariableValue(dyscope, vid);

		if (value == null)
			return new Pair<>(universe.falseExpression(), ResultType.NO);
		return this.checkReference(true,
				universe.reasoner(state.getPathCondition()),
				symbolicUtil.getSymRef(pointer), value);
	}

	/**
	 * Is the given reference applicable to the specified symbolic expression?
	 * 
	 * @param ref
	 *            The reference expression to be checked.
	 * @param value
	 *            The symbolic expression specified.
	 * @return True iff the given reference is applicable to the specified
	 *         symbolic expression
	 */
	private Triple<SymbolicExpression, BooleanExpression, ResultType> isValidRefOfValue(
			Reasoner reasoner, boolean derefable, ReferenceExpression ref,
			SymbolicExpression value) {
		BooleanExpression predicate = universe.falseExpression();

		if (ref.isIdentityReference())
			return new Triple<>(value, universe.trueExpression(),
					ResultType.YES);
		else {
			ReferenceExpression parent = ((NTReferenceExpression) ref)
					.getParent();
			Triple<SymbolicExpression, BooleanExpression, ResultType> parentTest = isValidRefOfValue(
					reasoner, derefable, parent, value);
			SymbolicExpression targetValue;

			if (parentTest.third != ResultType.YES)
				return parentTest;
			targetValue = parentTest.first;
			if (targetValue == null)
				return parentTest;
			if (ref.isArrayElementReference()) {
				ArrayElementReference arrayEleRef = (ArrayElementReference) ref;

				if (targetValue.type() instanceof SymbolicArrayType) {
					NumericExpression index = arrayEleRef.getIndex();
					NumericExpression length = universe.length(targetValue);

					if (targetValue.type() instanceof SymbolicCompleteArrayType) {
						BooleanExpression claim = derefable ? universe
								.lessThan(index, length) : universe
								.lessThanEquals(index, length);
						ResultType result = reasoner.valid(claim)
								.getResultType();

						claim = reasoner.simplify(claim);
						if (result == ResultType.YES) {
							if (!derefable
									&& reasoner.valid(
											universe.equals(length, index))
											.getResultType() != ResultType.NO) {
								return new Triple<>(null, claim, result);
							} else {
								return new Triple<>(universe.arrayRead(
										targetValue, index), claim, result);
							}
						} else if (result == ResultType.MAYBE)
							return new Triple<>(null, claim, result);
						predicate = claim;
					} else {
						return new Triple<>(universe.arrayRead(targetValue,
								index), universe.trueExpression(),
								ResultType.YES);
					}
				}
			} else if (ref.isTupleComponentReference()) {
				TupleComponentReference tupleCompRef = (TupleComponentReference) ref;

				if (targetValue.type() instanceof SymbolicTupleType) {
					IntObject index = tupleCompRef.getIndex();
					int length = ((SymbolicTupleType) targetValue.type())
							.sequence().numTypes();

					if (index.getInt() < length)
						return new Triple<>(universe.tupleRead(targetValue,
								index), universe.trueExpression(),
								ResultType.YES);
				}
			} else if (ref instanceof UnionMemberReference) {
				UnionMemberReference unionMemRef = (UnionMemberReference) ref;
				IntObject index = unionMemRef.getIndex();

				if (targetValue.type() instanceof SymbolicUnionType) {
					int length = ((SymbolicUnionType) targetValue.type())
							.sequence().numTypes();

					if (index.getInt() < length)
						return new Triple<>(universe.unionExtract(index,
								targetValue), universe.trueExpression(),
								ResultType.YES);
				}
			} else {
				// offset reference
				return new Triple<>(null, universe.trueExpression(),
						ResultType.YES);
			}
		}
		return new Triple<>(null, predicate, ResultType.NO);
	}

	/**
	 * 
	 * @param derefable
	 *            true iff to check derefableness; otherwise, only check
	 *            definedness.
	 * @param reasoner
	 * @param reference
	 * @param object
	 * @return
	 */
	private Pair<BooleanExpression, ResultType> checkReference(
			boolean derefable, Reasoner reasoner,
			ReferenceExpression reference, SymbolicExpression object) {
		Triple<SymbolicExpression, BooleanExpression, ResultType> result = isValidRefOfValue(
				reasoner, derefable, reference, object);

		return new Pair<>(result.second, result.third);
	}

	@Override
	public StringBuffer pathconditionToString(CIVLSource source, State state,
			String prefix, BooleanExpression pc) {
		BooleanExpression[] clauses = this.symbolicUtil
				.getConjunctiveClauses(pc);
		StringBuffer result = new StringBuffer();
		int length = clauses.length;

		for (int i = 0; i < length; i++) {
			result.append("\n");
			result.append(prefix);
			result.append(this.symbolicExpressionToString(source, state, null,
					clauses[i]));
		}
		return result;
	}

	@Override
	public Pair<BooleanExpression, ResultType> isDefinedPointer(State state,
			SymbolicExpression pointer) {
		if (this.symbolicUtil.isNullPointer(pointer))
			return new Pair<>(universe.trueExpression(), ResultType.YES);
		if (pointer.isNull())
			return new Pair<>(universe.falseExpression(), ResultType.NO);

		int dyscope = symbolicUtil.getDyscopeId(null, pointer);

		if (dyscope < 0)
			return new Pair<>(universe.falseExpression(), ResultType.NO);

		int vid = symbolicUtil.getVariableId(null, pointer);
		SymbolicExpression value = state.getVariableValue(dyscope, vid);

		if (value == null)
			return new Pair<>(universe.falseExpression(), ResultType.NO);
		return this.checkReference(false,
				universe.reasoner(state.getPathCondition()),
				symbolicUtil.getSymRef(pointer), value);
	}

	@Override
	public StringBuffer memoryUnitToString(State state, MemoryUnit mu) {
		return this.variableReferenceToString(state, null, true,
				mu.dyscopeID(), mu.varID(), mu.reference());
	}
}
