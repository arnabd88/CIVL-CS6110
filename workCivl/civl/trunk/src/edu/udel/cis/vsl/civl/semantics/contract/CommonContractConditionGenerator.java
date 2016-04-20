package edu.udel.cis.vsl.civl.semantics.contract;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.ContractConditionGenerator;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * This class is responsible for generating verification conditions and
 * reasoning conditions for contract clauses. Please read specification in
 * {@link ContractConditionGenerator} before read documents in this class.
 * 
 * @author ziqingluo
 *
 */
public class CommonContractConditionGenerator extends ContractEvaluator
		implements ContractConditionGenerator {

	/**
	 * String identifier for using uninterpreted functions to represent
	 * dereferencing valid pointers.
	 */
	private final StringObject DerefStrObject;

	/**
	 * String identifier for using uninterpreted functions to represent a
	 * boolean predicate stating a pointer is dereferable.
	 */
	private final StringObject IsValidStrObject;

	/**
	 * String identifier for using uninterpreted functions to represent numeric
	 * offset which is used for pointer accessing.
	 */
	private final NumericSymbolicConstant offsetConstantStrObj;

	/**
	 * String identifier for using uninterpreted functions to encoding a pointer
	 * type parameter as a symbolic pointer.
	 */
	private final StringObject pointerVariableIdentifier;

	/**
	 * String identifier for using uninterpreted functions to represent a
	 * pointer with a pair of a symbolic pointer and an offset.
	 */
	private final StringObject pointerStrObj;

	/**
	 * Symbolic pointer type: a tuple type
	 */
	private final SymbolicType pointerType;

	@SuppressWarnings("unused")
	private CIVLTypeFactory typeFactory;

	/*********** Verification conditions **********/
	/**
	 * A table of {@link independentMallocs}. An element of the table is indexed
	 * by a vid (see {@link Variable#setVid(int)}) and a pointer level.
	 * <p>
	 * This table saves information for symbolic pointers. The information is
	 * used to make symbolic pointers concrete, i.e. information about
	 * <code>malloc</code>.
	 * </p>
	 * 
	 * <p>
	 * This table is organized as follows:
	 * <ol>
	 * <li>Each row is indexed by vid which stands for a pointer type parameter.
	 * </li>
	 * <li>Elements in a row are indexed by "pointer level". Pointers with lower
	 * pointer levels must be concretized before ones with higher pointer
	 * levels.</li>
	 * <li>An element is a {@link independentMallocs}</li>
	 * </ol>
	 * 
	 * </p>
	 */
	private independentMallocs validPointerAxioms[][];

	/**
	 * An private class represents a set of mallocIDs which associate to a set
	 * of {@link MallocStatment} that are independent.
	 * 
	 * @author ziqingluo
	 *
	 */
	private class independentMallocs {
		private List<Integer> mallocSet;

		private independentMallocs() {
			mallocSet = new LinkedList<>();
		}
	}

	public CommonContractConditionGenerator(ModelFactory modelFactory,
			StateFactory stateFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, LibraryEvaluatorLoader loader,
			MemoryUnitFactory memUnitFactory, CIVLErrorLogger errorLogger,
			CIVLConfiguration config) {
		super(modelFactory, stateFactory, loader, symbolicUtil,
				symbolicAnalyzer, memUnitFactory, errorLogger, config);
		this.DerefStrObject = universe.stringObject("$deref");
		this.IsValidStrObject = universe.stringObject("$isValid");
		this.pointerStrObj = universe.stringObject("ptr");
		this.offsetConstantStrObj = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("offset"),
						universe.integerType());
		this.pointerVariableIdentifier = universe.stringObject("XP");
		this.pointerType = modelFactory.typeFactory().pointerSymbolicType();
		this.typeFactory = modelFactory.typeFactory();
		// this.savedAxioms = new LinkedList<>();
	}

	/**
	 * Re-organizes the given list of pairs of \valid operands and pointer
	 * levels into {@link #validPointerAxioms}. For how is it organized, see
	 * {@link #validPointerAxioms}.
	 * 
	 * @param validAxioms
	 *            Pairs of \valid operands and pointer levels.
	 */
	public void setValidConsequences(
			List<Pair<PointerSetExpression, Integer>> validAxioms) {
		int vidMax, colMax;
		List<Triple<Integer, Integer, Pair<PointerSetExpression, Integer>>> temp = new LinkedList<>();
		Set<Integer> avoidDuplicated = new HashSet<>(); // TODO: it is not
														// correct, malloc Ids
														// should store also via
														// PIDs

		vidMax = colMax = 0;
		for (Pair<PointerSetExpression, Integer> axiom : validAxioms) {
			LHSExpression pointer = axiom.left.getBasePointer();
			Variable rawVar = axiom.left.getBasePointer().variableWritten();
			int vid = rawVar.vid();
			int col = getPointerLevel((CIVLPointerType) rawVar.type())
					- getPointerLevel((CIVLPointerType) pointer
							.getExpressionType());

			vidMax = vidMax < vid ? vid : vidMax;
			colMax = colMax < col ? col : colMax;
			temp.add(new Triple<>(vid, col, axiom));
		}
		validPointerAxioms = new independentMallocs[vidMax + 1][colMax + 1];
		for (Triple<Integer, Integer, Pair<PointerSetExpression, Integer>> item : temp) {
			int vid = item.first;
			int col = item.second;
			Pair<PointerSetExpression, Integer> axiom = item.third;

			if (!avoidDuplicated.contains(axiom.right)) {
				avoidDuplicated.add(axiom.right);
				if (validPointerAxioms[vid][col] == null)
					validPointerAxioms[vid][col] = new independentMallocs();
				validPointerAxioms[vid][col].mallocSet.add(axiom.right);
			}
		}
	}

	@Override
	public List<Integer> getOrderedMallocId(int vid, int depth) {
		return validPointerAxioms[vid][depth].mallocSet;
	}

	/********************** Derive Contract Section ***************************/
	// TODO: under construction!!!
	public Evaluation deriveContract(FunctionContract contracts) {
		return null;
	}

	@SuppressWarnings("unused")
	private Evaluation deriveContractWorker(FunctionBehavior behavior) {
		return null;
	}

	/********************** Derive Expression Section ***************************/
	/*
	 * Derivation on some contract expressions: Derive some contract expressions
	 * to canonicalized uninterpreted functions so that CIVL can use reasoner to
	 * do reasoning.
	 */
	/**
	 * Derive an {@link Expression} to some reasonable form. e.g. an
	 * uninterpreted function. This method reuses
	 * {@link #evaluate(State, int, Expression)}. Thus we use the word
	 * "derivation" for those overrided semantics by this method, "evaluation"
	 * for semantics of the super method <br>
	 * Following is the list of explanations of the differences for some kinds
	 * of expressions between the evaluation and derivation:
	 * <p>
	 * <ol>
	 * <li>
	 * VALID operations (one of the UNARY operations): A valid operations will
	 * be derived to an uninterpreted function $valid(ptr, offset) where "ptr"
	 * is a symbolic pointer derived by
	 * {@link #parsePointer(State, int, Expression)} and "offset" is evaluated.</li>
	 * <li>DEREFERENCE expressions: An expression has the form <code>*x</code>
	 * will be derived to an uninterpreted function if the pointer is a symbolic
	 * pointer. see
	 * {@link #parseDereferencePointer(State, int, DereferenceExpression)}</li>
	 * </ol>
	 * </p>
	 * 
	 * @param state
	 * @param pid
	 * @param expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	public Evaluation deriveExpression(State state, int pid,
			Expression expression) throws UnsatisfiablePathConditionException {
		switch (expression.expressionKind()) {
		case UNARY:
			return deriveUnary(state, pid, (UnaryExpression) expression);
		default:
			return evaluate(state, pid, expression);
		}
	}

	@Override
	protected Evaluation evaluateRemoteExpression(State state, int pid,
			String process, BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression proc;
		Variable variable;
		NumericExpression procVal;
		SymbolicConstant varNameVal, result;
		SymbolicType varType, funcType;
		Evaluation eval;

		// derivation phase doesn't care remote expressions and results are not
		// saved in path conditions.
		proc = expression.right();
		eval = evaluate(state, pid, proc);
		state = eval.state;
		procVal = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("$" + proc.toString()),
				universe.integerType());
		variable = ((VariableExpression) expression.left()).variable();
		varType = variable.type().getDynamicType(universe);
		varNameVal = universe.symbolicConstant(
				universe.stringObject("$" + variable.name().name()), varType);
		funcType = universe.functionType(
				Arrays.asList(varType, universe.integerType()), varType);
		result = universe.symbolicConstant(universe.stringObject("\\remote"),
				funcType);
		eval.value = universe.apply(result, Arrays.asList(varNameVal, procVal));
		eval.state = state;
		return eval;
	}

	/**
	 * A worker method for {@link #deriveExpression(State, int, Expression)}.
	 * This method derives:
	 * <ol>
	 * <li>VALID operations</li>
	 * </ol>
	 * and evaluates the rest of others.
	 * 
	 * @param state
	 * @param pid
	 * @param expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation deriveUnary(State state, int pid,
			UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		UNARY_OPERATOR unaryOp = expression.operator();

		switch (unaryOp) {
		case VALID:
			return this.deriveValidOperatorExpression(state, pid, expression);
		default:
			return super.evaluateUnary(state, pid, expression);
		}
	}

	/**
	 * Derive an {@link UnaryExpression} whose operator is
	 * {@link UNARY_OPERATOR#VALID} to an uninterpreted representation. It uses
	 * quantifiers to represent a set of pointers.
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
	private Evaluation deriveValidOperatorExpression(State state, int pid,
			UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		PointerSetExpression mem = (PointerSetExpression) expression.operand();
		Evaluation eval;
		SymbolicExpression ptr, range;
		NumericExpression low, high;

		eval = evaluate(state, pid, mem.getBasePointer());
		state = eval.state;
		ptr = eval.value;
		if (mem.getRange() != null) {
			eval = evaluate(state, pid, mem.getRange());
			state = eval.state;
			range = eval.value;
			low = symbolicUtil.getLowOfRegularRange(range);
			high = symbolicUtil.getHighOfRegularRange(range);
		} else {
			low = universe.zeroInt();
			high = universe.oneInt();
		}
		eval.value = this.pointerIsValidForall(ptr, low, high);
		return eval;
	}

	/**
	 * Dereferencing on symbolic pointers will be derived to an uninterpreted
	 * function <code>$deref(ptr) where "ptr" is a symbolic pointer</code>; It
	 * will do concrete dereferencing if the pointer is concrete.
	 */
	@Override
	protected Evaluation evaluateDereference(State state, int pid,
			String process, DereferenceExpression expression)
			throws UnsatisfiablePathConditionException {
		Triple<State, SymbolicExpression, NumericExpression> derivedPointer = parsePointer(
				state, pid, expression.pointer());
		SymbolicExpression pointer;
		NumericExpression offset;

		state = derivedPointer.first;
		pointer = derivedPointer.second;
		offset = derivedPointer.third;
		if ((pointer.operator().equals(SymbolicOperator.TUPLE))) {
			return new Evaluation(state, pointer);
		} else if ((pointer.operator().equals(SymbolicOperator.LAMBDA))) {
			pointer = universe.apply(pointer, Arrays.asList(offset));
			SymbolicExpression val = derefOnPointer(pointer,
					expression.pointer());

			return new Evaluation(state, val);
		}
		throw new CIVLInternalException("unreachable", expression.getSource());
	}

	// TODO: idea: create a new kind : library behavior , loading library
	// components to deal with it.
	@Override
	public Evaluation deriveMPICollectiveBehavior(State state, int pid,
			int numProcess, MPICollectiveBehavior collectiveBehavior)
			throws UnsatisfiablePathConditionException {
		Expression communicator = collectiveBehavior.communicator();
		Evaluation eval = this.deriveExpression(state, pid, communicator);
		CIVLStructOrUnionType mpicommType;
		Iterator<StructOrUnionField> fieldIter;
		List<SymbolicType> structComponentTypes = new LinkedList<>();
		List<SymbolicExpression> structComponents = new LinkedList<>();
		SymbolicTupleType dynamicMpiCommType;
		SymbolicExpression dynamicMpiCommValue;

		assert communicator.getExpressionType().isStructType();
		mpicommType = (CIVLStructOrUnionType) communicator.getExpressionType();
		fieldIter = mpicommType.fields().iterator();
		while (fieldIter.hasNext()) {
			StructOrUnionField field = fieldIter.next();
			SymbolicExpression initVal;
			SymbolicType fieldType;

			fieldType = field.type().getDynamicType(universe);
			eval = havoc(state, fieldType);
			state = eval.state;
			initVal = eval.value;
			structComponentTypes.add(fieldType);
			structComponents.add(initVal);
		}
		dynamicMpiCommType = universe.tupleType(
				universe.stringObject(mpicommType.name().name()),
				structComponentTypes);
		dynamicMpiCommValue = universe.tuple(dynamicMpiCommType,
				structComponents);
		eval.state = state;
		eval.value = dynamicMpiCommValue;
		return eval;
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
					initializePointer(expression.variable()));
		} else
			return super.evaluateInitialValue(state, pid, expression);
	}

	/********************** Parse Pointer Section ***************************/
	/**
	 * To correctly derive a pointer type expression to a uninterpreted
	 * abstraction, this method provides a recursive translation for a pointer
	 * type expression e, without assuming any variable v appears in e has a
	 * defined value.
	 * 
	 * <p>
	 * To accomplish the goal, this method recursively does two things:
	 * <ol>
	 * <li>Parses a pointer-type expression to a symbolic pointer expression if
	 * it has to do so.</li>
	 * <li>Returns the value of a pointer-type expression e in a pointer
	 * addition form if it is derived to a symbolic pointer expression and e is
	 * not an lvalue.</li>
	 * </ol>
	 * Detailed specifications:
	 * <p>
	 * Symbolic pointer representation: Symbolic pointer will always be
	 * represented as <code>lambda int : offset,  ptr(pointer, offset)</code>
	 * where pointer is a symbolic pointer, offset is a bounded symbolic
	 * constant.
	 * </p>
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param pointer
	 *            The pointer type expression
	 * @return A {@link Triple} of (state, base pointer, offset)
	 * @throws UnsatisfiablePathConditionException
	 */
	private Triple<State, SymbolicExpression, NumericExpression> parsePointer(
			State state, int pid, Expression pointer)
			throws UnsatisfiablePathConditionException {
		ExpressionKind kind = pointer.expressionKind();

		switch (kind) {
		case BINARY:
			return parseBinaryPointer(state, pid, (BinaryExpression) pointer);
		case CAST:
			return parsePointer(state, pid,
					((CastExpression) pointer).getExpression());
		case DEREFERENCE:
			return parseDereferencePointer(state, pid,
					(DereferenceExpression) pointer);
		case SUBSCRIPT:
			return parseSubscriptPointer(state, pid,
					(SubscriptExpression) pointer);
		case VARIABLE:
			// pointer variable will either give you a concrete pointer or
			// a lambda symbolic pointer
			Variable var = ((VariableExpression) pointer).variable();
			SymbolicExpression varVal;

			varVal = initializePointer(var);
			return new Triple<>(state, varVal, universe.zeroInt());
		default:
			throw new CIVLUnimplementedFeatureException(
					"Derive on symbolic pointer expression :" + pointer,
					pointer.getSource());
		}
	}

	@Override
	public Evaluation pointerAdd(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression pointer,
			NumericExpression offset)
			throws UnsatisfiablePathConditionException {
		if (pointer.operator().equals(SymbolicOperator.LAMBDA)) {
			return new Evaluation(state, lambdaPointerAdd(pointer, offset));
		} else
			return super.pointerAdd(state, pid, process, expression, pointer,
					offset);
	}

	private Triple<State, SymbolicExpression, NumericExpression> parseDereferencePointer(
			State state, int pid, DereferenceExpression derefpointer)
			throws UnsatisfiablePathConditionException {
		Expression pointer = derefpointer.pointer();
		Triple<State, SymbolicExpression, NumericExpression> result;
		SymbolicExpression symPointer;
		NumericExpression symOffset;
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		result = parsePointer(state, pid, pointer);
		symPointer = result.second;
		symOffset = result.third;
		if (symPointer.operator().equals(SymbolicOperator.LAMBDA)) {
			result.second = universe.apply(result.second,
					Arrays.asList(result.third));
			result.second = this.derefOnPointer(result.second, pointer);
			result.third = universe.zeroInt();
		} else {
			Evaluation eval = evaluatePointerAdd(state, process, symPointer,
					symOffset, false, pointer.getSource()).left;

			eval = this.dereference(derefpointer.getSource(), eval.state,
					process, pointer, eval.value, false);
			result.first = eval.state;
			result.second = eval.value;
			result.third = universe.zeroInt();
		}
		return result;
	}

	private Triple<State, SymbolicExpression, NumericExpression> parseSubscriptPointer(
			State state, int pid, SubscriptExpression pointer)
			throws UnsatisfiablePathConditionException {
		Expression array = pointer.array();
		Expression index = pointer.index();
		Triple<State, SymbolicExpression, NumericExpression> result;
		Evaluation eval;

		result = parsePointer(state, pid, array);
		eval = evaluate(state, pid, index);
		result.first = eval.state;
		result.third = (NumericExpression) eval.value;
		return result;
	}

	private Triple<State, SymbolicExpression, NumericExpression> parseBinaryPointer(
			State state, int pid, BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression left, right;
		NumericExpression offsetValue;
		Triple<State, SymbolicExpression, NumericExpression> result;
		Evaluation eval;

		left = expression.left();
		right = expression.right();
		assert expression.operator() == BINARY_OPERATOR.POINTER_ADD;
		if (left.getExpressionType().isPointerType()) {
			result = parsePointer(state, pid, left);
			eval = evaluate(state, pid, right);
			state = eval.state;
			offsetValue = (NumericExpression) eval.value;
		} else {
			result = parsePointer(state, pid, right);
			eval = evaluate(state, pid, left);
			state = eval.state;
			offsetValue = (NumericExpression) eval.value;
		}
		result.first = state;
		result.third = universe.add(result.third, offsetValue);
		return result;
	}

	private SymbolicExpression lambdaPointerAdd(SymbolicExpression pointer,
			NumericExpression offset) {
		assert pointer.operator() == SymbolicOperator.LAMBDA;// pre-condition
		// optimization:
		if (offset.isZero())
			return pointer;

		NumericSymbolicConstant newConst = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"),
						universe.integerType());
		SymbolicExpression addition = universe.add(newConst, offset);

		return universe.lambda(newConst,
				universe.apply(pointer, Arrays.asList(addition)));
	}

	/****************************************************************************
	 * Encoding methods: Here "encoding" means saving informations into some
	 * reasonable predicates and symbols, so that CIVL can do derivation and
	 * reasoning on some contracts:
	 ****************************************************************************/
	@Override
	public SymbolicExpression derefOnPointer(SymbolicExpression pointer,
			Expression pointerExpr) {
		CIVLType objType = ((CIVLPointerType) pointerExpr.getExpressionType())
				.baseType();
		SymbolicFunctionType derefFuncType = universe.functionType(
				Arrays.asList(pointerType), objType.getDynamicType(universe));
		SymbolicConstant derefFunc = universe.symbolicConstant(DerefStrObject,
				derefFuncType);
		SymbolicExpression afterDeref = universe.apply(derefFunc,
				Arrays.asList(pointer));

		if (!objType.isPointerType())
			return afterDeref;
		else {
			return this.initializePointer(afterDeref, offsetConstantStrObj);
		}
	}

	private SymbolicExpression initializePointer(
			SymbolicExpression pointerVarIdentifier,
			NumericSymbolicConstant offset) {
		SymbolicFunctionType ptrLambdaType;
		SymbolicExpression ptrLambda;
		SymbolicConstant ptrFunc;

		// lambda type [ptr, integer] => ptr:
		ptrLambdaType = universe
				.functionType(
						Arrays.asList(pointerType, universe.integerType()),
						pointerType);
		ptrFunc = universe.symbolicConstant(pointerStrObj, ptrLambdaType);
		ptrLambda = universe.lambda(
				offset,
				universe.apply(ptrFunc,
						Arrays.asList(pointerVarIdentifier, offset)));
		return ptrLambda;
	}

	public SymbolicExpression initializePointer(Variable pointerVar) {
		NumericSymbolicConstant offset = this.offsetConstantStrObj;
		SymbolicFunctionType sidvid2ptr = universe.functionType(
				Arrays.asList(universe.integerType(), universe.integerType()),
				pointerType);
		SymbolicConstant varIdent = universe.symbolicConstant(
				pointerVariableIdentifier, sidvid2ptr);
		SymbolicExpression ptrVal = universe.apply(
				varIdent,
				Arrays.asList(universe.integer(pointerVar.vid()),
						universe.integer(pointerVar.scope().id())));

		return this.initializePointer(ptrVal, offset);
	}

	@Override
	public BooleanExpression pointerIsValid(SymbolicExpression basePointer) {
		SymbolicFunctionType isValidFuncType = universe.functionType(
				Arrays.asList(pointerType), universe.booleanType());
		SymbolicConstant validAbstractFunc = universe.symbolicConstant(
				IsValidStrObject, isValidFuncType);
		BooleanExpression predicate = (BooleanExpression) universe.apply(
				validAbstractFunc, Arrays.asList(basePointer));
		return predicate;
	}

	@Override
	public BooleanExpression pointerIsValidForall(
			SymbolicExpression basePointer, NumericExpression low,
			NumericExpression high) {
		NumericSymbolicConstant idx = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"),
						universe.integerType());
		SymbolicFunctionType validFuncType;
		SymbolicConstant validAbstractFunc;
		BooleanExpression predicate;

		validFuncType = universe.functionType(Arrays.asList(pointerType),
				universe.booleanType());
		validAbstractFunc = universe.symbolicConstant(IsValidStrObject,
				validFuncType);
		if (basePointer.operator().equals(SymbolicOperator.LAMBDA)) {
			SymbolicExpression pointer;

			pointer = universe.apply(basePointer, Arrays.asList(idx));
			predicate = (BooleanExpression) universe.apply(validAbstractFunc,
					Arrays.asList(pointer));
		} else {
			predicate = (BooleanExpression) universe.apply(validAbstractFunc,
					Arrays.asList(basePointer));
		}
		// universe.forallInt takes low and high as [low, high):
		return universe.forallInt(idx, low,
				universe.add(high, universe.oneInt()), predicate);
	}

	/****************************************************************************
	 * Decoding methods: Here "decoding" means extracting informations from some
	 * predicates and symbols. For many concrete informations such as concrete
	 * pointer value, it will simplifies the execution if we apply these
	 * informations directly onto CIVL states.
	 ****************************************************************************/
	/**
	 * see {@link #getPointerLevel(SymbolicExpression)} a pointer to a primitive
	 * type has length 0.
	 * 
	 * @param pointerType
	 * @return
	 */
	private int getPointerLevel(CIVLPointerType pointerType) {
		int length = 0;
		CIVLType baseType = pointerType.baseType();

		while (baseType.isPointerType()) {
			CIVLPointerType temp = (CIVLPointerType) baseType;

			length++;
			baseType = temp.baseType();
		}
		return length;
	}

	/******************* Miscellaneous interface implementations **********************/
	@Override
	public Iterator<List<Integer>> validPointersIterator() {
		int vidB = validPointerAxioms.length;

		if (vidB <= 0)
			return null;
		return new Iterator<List<Integer>>() {
			int nextVid = 0;
			int nextLevel = 0;
			final int myVidB = vidB;

			@Override
			public boolean hasNext() {
				return !(nextVid < 0);
			}

			@Override
			public List<Integer> next() {
				if (nextVid >= 0) {
					int levelB = validPointerAxioms[nextVid].length;
					independentMallocs ret;

					ret = validPointerAxioms[nextVid][nextLevel++];
					if (nextLevel >= levelB) {
						// Looking for nextVid:
						while (++nextVid < myVidB)
							if (validPointerAxioms[nextVid] != null)
								break;
						if (nextVid < myVidB)
							nextLevel = 0;
						else
							nextVid = -1;
					}
					return ret == null ? new LinkedList<>() : ret.mallocSet;
				} else
					return null;
			}
		};
	}

	/**
	 * Override, because in derivation phase, it doesn't need to consider MPI
	 * contract expression, just make them dummy expressions.
	 */
	@Override
	protected Evaluation evaluateMPIContractExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		// TODO: need a better dummy represatation or fixing
		// assumptionAsInterval can help this:

		return new Evaluation(state, universe.symbolicConstant(universe
				.stringObject(expression.toString()), expression
				.getExpressionType().getDynamicType(universe)));
	}
}
