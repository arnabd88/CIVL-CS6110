package edu.udel.cis.vsl.civl.library.time;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class LibtimeExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	// private SymbolicConstant timeFunc;
	private SymbolicConstant localtimeFunc;
	private CIVLType tmType;
	private SymbolicType tmSymbolicType;
	// private SymbolicType stringSymbolicType;
	private SymbolicConstant tmToStrFunc;
	private SymbolicArrayType stringSymbolicType;
	private SymbolicConstant tmToStrSizeFunc;

	public LibtimeExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
		this.tmType = this.typeFactory.systemType(ModelConfiguration.TM_TYPE);
		if (tmType != null)
			this.tmSymbolicType = tmType.getDynamicType(universe);
		this.stringSymbolicType = (SymbolicArrayType) universe.canonic(universe
				.arrayType(universe.characterType()));
		// this.timeFunc = (SymbolicConstant) universe.canonic(universe
		// .symbolicConstant(
		// universe.stringObject("time"),
		// universe.functionType(
		// Arrays.asList(universe.integerType()),
		// universe.realType())));
		if (tmType != null)
			this.localtimeFunc = (SymbolicConstant) universe.canonic(universe
					.symbolicConstant(universe.stringObject("localtime"),
							universe.functionType(
									Arrays.asList(universe.realType()),
									this.tmSymbolicType)));
		if (tmType != null)
			this.tmToStrFunc = (SymbolicConstant) universe.canonic(universe
					.symbolicConstant(universe.stringObject("strftime"),
							universe.functionType(Arrays.asList(
									universe.integerType(),
									typeFactory.pointerSymbolicType(),
									this.tmSymbolicType),
									this.stringSymbolicType)));
		if (tmType != null)
			this.tmToStrSizeFunc = (SymbolicConstant) universe.canonic(universe
					.symbolicConstant(universe.stringObject("strftimeSize"),
							universe.functionType(Arrays.asList(
									universe.integerType(),
									typeFactory.pointerSymbolicType(),
									this.tmSymbolicType), universe
									.integerType())));
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		CallOrSpawnStatement call;
		int numArgs;

		call = (CallOrSpawnStatement) statement;
		numArgs = call.arguments().size();
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
		case "localtime":
			state = this.executeLocalTime(state, pid, call.lhs(), arguments,
					argumentValues);
			break;
		case "strftime":
			state = this.executeStrftime(state, pid, call.lhs(), arguments,
					argumentValues);
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"execution of function " + name + " in time library");
		}
		state = stateFactory.setLocation(state, pid, statement.target());
		return state;
	}

	/**
	 * <pre>
	 * size_t strftime(char * restrict s,
	 *               size_t maxsize,
	 *               const char * restrict format,
	 *               const struct tm * restrict timeptr);
	 * </pre>
	 * 
	 * @param state
	 * @param pid
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeStrftime(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		// TODO Auto-generated method stub
		// @SuppressWarnings("unused")
		SymbolicExpression resultPointer = argumentValues[0];
		String process = state.getProcessState(pid).name();
		Evaluation eval = this.evaluator.dereference(arguments[3].getSource(),
				state, process, arguments[3], argumentValues[3], false);
		SymbolicExpression tmValue, sizeValue, tmStr;

		resultPointer = this.symbolicUtil.parentPointer(
				arguments[0].getSource(), resultPointer);
		state = eval.state;
		tmValue = eval.value;
		tmStr = universe.apply(tmToStrFunc,
				Arrays.asList(argumentValues[1], argumentValues[2], tmValue));
		state = this.primaryExecutor.assign(arguments[0].getSource(), state,
				process, resultPointer, tmStr);
		sizeValue = universe.apply(tmToStrSizeFunc,
				Arrays.asList(argumentValues[1], argumentValues[2], tmValue));
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					sizeValue);
		return state;
	}

	/**
	 * <pre>
	 * #include <time.h>
	 * struct tm *localtime(const time_t *timer);
	 * 
	 * Description
	 * The localtime function converts the calendar time pointed to by timer 
	 * into a broken-down time, expressed as local time.
	 * 
	 * Returns
	 * The localtime function returns a pointer to the broken-down time, 
	 * or a null pointer if the specified time cannot be converted to 
	 * local time.
	 * </pre>
	 * 
	 * @param state
	 * @param pid
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeLocalTime(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		String process = state.getProcessState(pid).name();
		Evaluation eval = this.evaluator.dereference(arguments[0].getSource(),
				state, process, arguments[0], argumentValues[0], false);
		SymbolicExpression result;
		// Pair<State, SymbolicExpression> tmObjtResult;
		Variable brokenTimeVar = this.modelFactory.brokenTimeVariable();
		SymbolicExpression brokenTimePointer;

		state = eval.state;
		result = universe.apply(localtimeFunc, Arrays.asList(eval.value));
		state = this.stateFactory
				.setVariable(state, brokenTimeVar, pid, result);
		// //TODO
		// tmObjtResult = this.primaryExecutor.malloc(lhs.getSource(), state,
		// pid,
		// process,
		// modelFactory.hereOrRootExpression(lhs.getSource(), true),
		// modelFactory.scopeValue(0),
		// modelFactory.getSystemType(Model.TM_TYPE), result);
		// /
		// state = tmObjtResult.left;
		brokenTimePointer = this.symbolicUtil.makePointer(
				state.getDyscope(pid, brokenTimeVar.scope()),
				brokenTimeVar.vid(), universe.identityReference());
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					brokenTimePointer);
		return state;
	}

	// private State executeTime(State state, int pid, LHSExpression lhs,
	// Expression[] arguments, SymbolicExpression[] argumentValues)
	// throws UnsatisfiablePathConditionException {
	// Variable timeCountVar = this.modelFactory.timeCountVariable();
	// NumericExpression timeCountValue = (NumericExpression) state.valueOf(
	// pid, timeCountVar);
	// NumericExpression timeValue = (NumericExpression) universe.apply(
	// timeFunc, Arrays.asList(timeCountValue));
	// BooleanExpression timeValueAssumption, newPathCondition;
	//
	// state = this.stateFactory.setVariable(state, timeCountVar, pid,
	// universe.add(timeCountValue, this.one));
	// // if(time_count == 0) $assume timeValue > 0;
	// if (timeCountValue.isZero()) {
	// timeValueAssumption = universe.lessThan(universe.zeroReal(),
	// timeValue);
	// } else {
	// // if(time_count > 0) $assume timeValue > time(time_count - 1);
	// timeValueAssumption = universe.lessThan(
	// (NumericExpression) universe.apply(timeFunc, Arrays
	// .asList(universe.subtract(timeCountValue, one))),
	// timeValue);
	// }
	// if (lhs != null)
	// state = this.primaryExecutor.assign(state, pid, state
	// .getProcessState(pid).name(), lhs, timeValue);
	// if (!symbolicUtil.isNullPointer(argumentValues[0]))
	// state = this.primaryExecutor.assign(arguments[0].getSource(),
	// state, state.getProcessState(pid).name(),
	// argumentValues[0], timeValue);
	// newPathCondition = universe.and(state.getPathCondition(),
	// timeValueAssumption);
	// state = state.setPathCondition(newPathCondition);
	// return state;
	// }
}
