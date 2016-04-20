package edu.udel.cis.vsl.civl.library.omp;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.IF.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class LibompExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	private CIVLType ompLoopInfoType;

	private SymbolicType dynamicOmpLoopInfoType;

	private CIVLType ompSectionsInfoType;

	private SymbolicType dynamicOmpSectionsInfoType;

	public LibompExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			CIVLConfiguration civlConfig) {
		super(name, primaryExecutor, modelFactory, symbolicUtil, civlConfig);
		ompLoopInfoType = model.function("$omp_ws_arrive_loop").functionType()
				.returnType();
		dynamicOmpLoopInfoType = ompLoopInfoType.getDynamicType(universe);
		ompSectionsInfoType = model.function("$omp_ws_arrive_sections")
				.functionType().returnType();
		dynamicOmpSectionsInfoType = ompSectionsInfoType
				.getDynamicType(universe);
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
	}

	private State executeWork(State state, int pid, CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		int numArgs = call.arguments().size();
		String functionName = call.function().name().name();
		LHSExpression lhs = call.lhs();
		CIVLSource source = call.getSource();
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = call.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (functionName) {
		case "barrier_and_flush":
			state = executeBarrierAndFlush(source, state, numArgs, arguments,
					argumentValues);
			break;
		case "$omp_gws_create":
			state = executeGwsCreate(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$omp_gws_destroy":
		case "$omp_ws_destroy":
			state = executeFree(state, pid, process, arguments, argumentValues,
					call.getSource());
			break;
		case "$omp_ws_create":
			state = executeWsCreate(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$omp_ws_arrive_loop":
			state = executeArrriveLoop(source, state, numArgs, lhs, arguments,
					argumentValues);
			break;
		case "$omp_ws_arrive_sections":
			state = executeArrriveSections(source, state, numArgs, lhs,
					arguments, argumentValues);
			break;
		case "$omp_ws_arrive_single":
			state = executeArrriveSingle(source, state, numArgs, lhs,
					arguments, argumentValues);
			break;
		case "$omp_ws_arrive_barrier":
			state = executeArrriveBarrier(source, state, numArgs, lhs,
					arguments, argumentValues);
			break;
		default:
			throw new CIVLUnimplementedFeatureException("The function "
					+ functionName + " is not supported in " + name + ".h.",
					source);

		}
		state = stateFactory.setLocation(state, pid, call.target());
		return state;
	}

	/**
	 * Executes barrier_and_flush(), which Does a barrier on _barrier and a
	 * flush on all shared variables. After this completes, all local copies
	 * will agree with each other and with the shared copy of the variable, and
	 * all state variables will be -1.
	 * 
	 * @param source
	 *            The source code element to be used for error report.
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
	 * @return the new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeBarrierAndFlush(CIVLSource source, State state,
			int pid, Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		// TODO implement barrier_and_flush()
		return state;
	}

	/**
	 * <p>
	 * Executes $omp_gws_create($scope scope, int nthreads) which creates new
	 * global work-sharing state object, returning handle to it. nthreads is the
	 * number of threads in the parallel region. There is one of these per
	 * parallel region, created upon entering the region.
	 * </p>
	 * 
	 * Here is the definition of $omp_gws:
	 * 
	 * <pre>
	 * typedef struct __omp_gws__ {
	 *   int nthreads;
	 *   _Bool isInit[];
	 *   CIVL_omp_loop_info loops[];
	 *   CIVL_omp_sections_info sections[];
	 * } $omp_gws;
	 * </pre>
	 * 
	 * @param source
	 *            The source code element to be used for error report.
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
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeGwsCreate(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		// the gws object to be created
		SymbolicExpression gwsObj;
		// the CIVL type of __omp_gws__
		CIVLType gwsType = model.ompGwsType();
		// the representation of the CIVL type of __omp_gws__ in SARL
		SymbolicType dynamicGwsType = gwsType.getDynamicType(universe);
		// the value of the first argument, which is scope.
		SymbolicExpression scope = argumentValues[0];
		// the CIVL expression of the first argument of the function call
		Expression scopeExpression = arguments[0];
		// the value of the second argument, which is nthread.
		SymbolicExpression nthreads = argumentValues[1];
		// the second field isInit of the __omp_gws__ object to be created
		SymbolicExpression isInit;
		// the representation of false in SARL
		SymbolicExpression falseValue = universe.canonic(universe.bool(false));
		// the list of components of the array isInit
		List<SymbolicExpression> isInitComponents = new LinkedList<>();
		// the third field loops of the __omp_gws__ object to be created
		SymbolicExpression loops = universe.array(this.dynamicOmpLoopInfoType,
				new LinkedList<SymbolicExpression>());
		// the last field sections of the __omp_gws__ object to be created
		SymbolicExpression sections = universe.array(
				this.dynamicOmpSectionsInfoType,
				new LinkedList<SymbolicExpression>());
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		// try to infer the concrete value of nthreads
		IntegerNumber number_nthreads = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) nthreads);

		if (number_nthreads != null) {
			// nthreads is concrete
			int int_nthreads = number_nthreads.intValue();

			// isInit component
			for (int i = 0; i < int_nthreads; i++) {
				isInitComponents.add(falseValue);
			}
			isInit = universe.array(universe.booleanType(), isInitComponents);
		} else {
			// nthreads is symbolic, use array lambda to initialize isInit.
			SymbolicCompleteArrayType arrayType;
			NumericSymbolicConstant index;
			SymbolicExpression initFunction;
			SymbolicType integerType = modelFactory.integerType()
					.getDynamicType(universe);

			arrayType = universe.arrayType(universe.booleanType(),
					(NumericExpression) nthreads);
			index = (NumericSymbolicConstant) universe.symbolicConstant(
					universe.stringObject("i"), integerType);
			// initFunction(i): isInit[i] = false;
			initFunction = universe.lambda(index, falseValue);
			isInit = universe.arrayLambda(arrayType, initFunction);
		}
		// creates the __omp_gws__ object as a tuple using the four elements in
		// order specified above: nthreads, isInit, loops, sections.
		gwsObj = universe.tuple((SymbolicTupleType) dynamicGwsType,
				Arrays.asList(nthreads, isInit, loops, sections));
		// malloc a memory unit in the heap of the given scope to store the
		// newly created __omp_gws__ object, and assign lhs with the
		// corresponding handle $omp_gws, which is in fact a pointer to the
		// __omp_gws__ object.
		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				scopeExpression, scope, gwsType, gwsObj);
		return state;
	}

	/**
	 * <p>
	 * Executes $omp_ws_create($scope scope, $omp_gws, int tid) which creates a
	 * local work-sharing object, which is basically a pair consisting of a
	 * global work-sharing handle and a thread id.
	 * </p>
	 * 
	 * Here is the definition of $omp_ws:
	 * 
	 * <pre>
	 * typedef struct __omp_ws__ {
	 *   int tid;
	 *   $omp_gws gws;
	 * } $omp_ws;
	 * </pre>
	 * 
	 * @param source
	 *            The source code element to be used for error report.
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
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeWsCreate(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression gws = argumentValues[1];
		SymbolicExpression gwsObj;
		SymbolicExpression wsObj;
		CIVLType wsType = model.ompWsType();
		SymbolicType dynamicWsType = wsType.getDynamicType(universe);
		SymbolicExpression tid = argumentValues[2];
		SymbolicExpression isInit;
		Evaluation eval;

		eval = this.evaluator.dereference(arguments[1].getSource(), state,
				process, gws, false);
		state = eval.state;
		gwsObj = eval.value;
		isInit = universe.tupleRead(gwsObj, oneObject);
		// TODO report an error if the place has already been taken by other
		// processes.
		assert universe.arrayRead(isInit, (NumericExpression) tid).equals(
				universe.bool(false));
		isInit = universe.arrayWrite(isInit, (NumericExpression) tid,
				universe.bool(true));
		gwsObj = universe.tupleWrite(gwsObj, oneObject, isInit);
		state = this.primaryExecutor.assign(arguments[1].getSource(), state,
				process, gws, gwsObj);
		wsObj = universe.tuple((SymbolicTupleType) dynamicWsType,
				Arrays.asList(tid, gws));
		state = this.primaryExecutor.malloc(source, state, pid, process, lhs,
				scopeExpression, scope, wsType, wsObj);
		return state;
	}

	private State executeArrriveLoop(CIVLSource source, State state, int pid,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		// TODO implement barrier_and_flush()
		return state;
	}

	private State executeArrriveSections(CIVLSource source, State state,
			int pid, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		// TODO implement omp_ws_arrive_sections()
		return state;
	}

	private State executeArrriveSingle(CIVLSource source, State state, int pid,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		// TODO implement omp_ws_arrive_single()
		return state;
	}

	private State executeArrriveBarrier(CIVLSource source, State state,
			int pid, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		// TODO implement omp_ws_arrive_barrier()
		return state;
	}
}
