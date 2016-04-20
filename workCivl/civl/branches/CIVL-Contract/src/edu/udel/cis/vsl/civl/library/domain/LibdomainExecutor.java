package edu.udel.cis.vsl.civl.library.domain;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

public class LibdomainExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	public LibdomainExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement call,
			String functionName) throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		LHSExpression lhs;
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		numArgs = call.arguments().size();
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
		switch (functionName) {
		case "$dimension_of":
			state = execute_dimension_of(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$domain_partition":
			state = execute_domain_partition(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$high_of_regular_range":
			state = execute_high_of_regular_range(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$is_rectangular_domain":
			state = execute_is_rectangular_domain(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$is_regular_range":
			state = execute_is_regular_range(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$low_of_regular_range":
			state = execute_low_of_regular_range(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$range_of_rectangular_domain":
			state = execute_range_of_rectangular_domain(state, pid, process,
					lhs, arguments, argumentValues, call.getSource());
			break;
		case "$step_of_regular_range":
			state = execute_step_of_regular_range(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		}
		state = stateFactory.setLocation(state, pid, call.target(),
				call.lhs() != null);
		return state;
	}

	private State execute_dimension_of(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					this.symbolicUtil.getDimensionOf(argumentValues[0]));
		return state;
	}

	private State execute_range_of_rectangular_domain(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		int index = this.symbolicUtil.extractInt(source,
				(NumericExpression) argumentValues[1]);

		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					this.symbolicUtil.getRangeOfRectangularDomain(
							argumentValues[0], index));
		return state;
	}

	private State execute_is_rectangular_domain(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					universe.bool(this.symbolicUtil
							.isRectangularDomain(argumentValues[0])));
		return state;
	}

	private State execute_is_regular_range(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					universe.bool(this.symbolicUtil
							.isRegularRange(argumentValues[0])));
		return state;
	}

	private State execute_step_of_regular_range(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					this.symbolicUtil.getStepOfRegularRange(argumentValues[0]));
		return state;
	}

	private State execute_low_of_regular_range(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					this.symbolicUtil.getLowOfRegularRange(argumentValues[0]));

		return state;
	}

	private State execute_high_of_regular_range(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					this.symbolicUtil.getHighOfRegularRange(argumentValues[0]));

		return state;
	}

	/**
	 * Executes the domain_partition statement. Returns a object with type of
	 * struct "$domian_decomposition"
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The information of the process
	 * @param lhs
	 *            The left-hand side expression
	 * @param arguments
	 *            The expressions of arguments
	 * @param argumentValues
	 *            The symbolic expressions of arguments
	 * @param source
	 *            The CIVL source of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_domain_partition(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression domain = argumentValues[0];
		NumericExpression strategy = (NumericExpression) argumentValues[1];
		NumericExpression numParts = (NumericExpression) argumentValues[2];
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber strategy_num = (IntegerNumber) reasoner
				.extractNumber(strategy), numParts_num = (IntegerNumber) reasoner
				.extractNumber(numParts);
		int strategy_int, numParts_int;
		List<SymbolicExpression> subDomains = null;
		SymbolicTupleType resultType;
		SymbolicExpression result;

		if (strategy_num == null) {
			this.errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"$domain_partition requires a concrete strategy argument");
			throw new UnsatisfiablePathConditionException();
		}
		if (numParts_num == null) {
			this.errorLogger
					.logSimpleError(source, state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.OTHER,
							"$domain_partition requires a concrete number of partitions argument");
			throw new UnsatisfiablePathConditionException();
		}
		strategy_int = strategy_num.intValue();
		numParts_int = numParts_num.intValue();
		switch (strategy_int) {
		default:
		case ModelConfiguration.DECOMP_ROUND_ROBIN:
			subDomains = this.domainPartition_round_robin(domain, numParts_int);
			break;
		}
		resultType = universe.tupleType(
				universe.stringObject("$domain_decomposition"),
				Arrays.asList(universe.integerType(),
						universe.arrayType(domain.type(), numParts)));
		result = universe.tuple(
				resultType,
				Arrays.asList(numParts,
						universe.array(domain.type(), subDomains)));
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					result);
		return state;
	}

	/**
	 * Do a domain partition based on the robin strategy.
	 * 
	 * @param domain
	 *            The symbolic expression of the domain.
	 * @param number
	 *            The number of the partitions.
	 * @return
	 */
	private List<SymbolicExpression> domainPartition_round_robin(
			SymbolicExpression domain, int number) {

		if (number == 1)
			return Arrays.asList(domain);
		else {
			Map<Integer, List<SymbolicExpression>> partitions = new HashMap<>(
					number);
			List<SymbolicExpression> current = symbolicUtil
					.getDomainInit(domain);
			int id = 0;
			List<SymbolicExpression> result = new LinkedList<>();
			Iterator<List<SymbolicExpression>> domIter = symbolicUtil
					.getDomainIterator(domain);
			CIVLType rangeType = this.typeFactory.rangeType();
			CIVLDomainType civlDomType = this.typeFactory.domainType(rangeType);
			SymbolicTupleType domType = (SymbolicTupleType) civlDomType
					.getDynamicType(universe);
			SymbolicUnionType domUnionType = civlDomType
					.getDynamicSubTypesUnion(universe);
			SymbolicExpression myDomain, myLiterals;
			SymbolicType domainElementType = symbolicUtil
					.getDomainElementType(domain);
			NumericExpression dim = (NumericExpression) universe.tupleRead(
					domain, zeroObject);

			while (domIter.hasNext()) {
				SymbolicExpression element;
				List<SymbolicExpression> partitionedElements;

				current = domIter.next();
				element = universe.array(universe.integerType(), current);
				if (partitions.containsKey(id)) {
					partitionedElements = partitions.get(id);

					partitionedElements.add(element);
				} else {
					partitionedElements = new LinkedList<SymbolicExpression>();
					partitionedElements.add(element);
					partitions.put(id, partitionedElements);
				}
				id = (id + 1) % number;
			}
			// Making all integer-elements entries be a literal domain
			for (int i = 0; i < number; i++) {
				List<SymbolicExpression> myPartition = partitions.get(i);
				SymbolicExpression elementsArray;

				if (myPartition != null)
					elementsArray = universe.array(domainElementType,
							myPartition);
				else {
					elementsArray = universe.emptyArray(domainElementType);
				}
				myLiterals = universe.unionInject(domUnionType, oneObject,
						elementsArray);
				myDomain = universe.tuple(domType,
						Arrays.asList(dim, one, myLiterals));
				result.add(myDomain);
			}
			return result;
		}
	}
}
