package edu.udel.cis.vsl.civl.library.pthread;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;


public class LibpthreadExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {


	public LibpthreadExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig);
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
	}

	private State executeWork(State state, int pid,
			CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		int numArgs;
		CIVLSource source = statement.getSource();
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		numArgs = statement.arguments().size();
		name = statement.function().name();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = statement.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (name.name()) {
		case "_add_thread":
			state = execute_add_thread(state, pid, process, arguments,
					argumentValues, source);
			break;
		default:
		}
		state = stateFactory.setLocation(state, pid, statement.target());
		return state;
	}

	private State execute_add_thread(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression poolPointer = argumentValues[0];
		SymbolicExpression threadPointer = argumentValues[1];
		CIVLSource poolPointerSource = arguments[0].getSource();
		SymbolicExpression pool;
		Evaluation eval = evaluator.dereference(poolPointerSource, state,
				process, poolPointer, false);
		NumericExpression len;
		SymbolicExpression threads;

		pool = eval.value;
		state = eval.state;
		len = (NumericExpression) universe.tupleRead(pool, oneObject);
		threads = universe.tupleRead(pool, zeroObject);
		threads = universe.append(threads, threadPointer);
		len = universe.add(len, one);
		pool = universe.tupleWrite(pool, zeroObject, threads);
		pool = universe.tupleWrite(pool, oneObject, len);
		state = primaryExecutor.assign(poolPointerSource, state, process,
				poolPointer, pool);
		return state;
	}

}
