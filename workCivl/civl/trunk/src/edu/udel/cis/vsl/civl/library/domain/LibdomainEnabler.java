package edu.udel.cis.vsl.civl.library.domain;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.Transition.AtomicLockAction;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;

public class LibdomainEnabler extends BaseLibraryEnabler implements
		LibraryEnabler {

	public LibdomainEnabler(String name, Enabler primaryEnabler,
			Evaluator evaluator, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			CIVLConfiguration civlConfig,
			LibraryEnablerLoader libEnablerLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryEnabler, evaluator, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libEnablerLoader,
				libEvaluatorLoader);
	}

	@Override
	public List<Transition> enabledTransitions(State state,
			CallOrSpawnStatement call, BooleanExpression pathCondition,
			int pid, int processIdentifier, AtomicLockAction atomicLockAction)
			throws UnsatisfiablePathConditionException {
		String functionName = call.function().name().name();
		try {
			switch (functionName) {
			case "$domain_partition":
				return this.enabledDomainPartition(state, call, pathCondition,
						pid, processIdentifier, atomicLockAction);
			default:
				return super.enabledTransitions(state, call, pathCondition,
						pid, processIdentifier, atomicLockAction);
			}
		} catch (LibraryLoaderException e) {
			throw new CIVLInternalException("Domain library loader fails",
					call.getSource());
		}
	}

	/* *************************** Private Methods ************************* */

	private List<Transition> enabledDomainPartition(State state,
			CallOrSpawnStatement call, BooleanExpression pathCondition,
			int pid, int processIdentifier, AtomicLockAction atomicLockAction)
			throws UnsatisfiablePathConditionException, LibraryLoaderException {
		List<Statement> statements = new LinkedList<>();
		List<Transition> transitions = new LinkedList<>();
		Expression[] arguments = new Expression[3];
		SymbolicExpression strategy;
		SymbolicExpression nthreads;
		SymbolicExpression domain;
		Evaluation eval;
		Number strategyNum;
		int strategyInt;
		Reasoner reasoner = universe.reasoner(pathCondition);
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		call.arguments().toArray(arguments);
		// arguments: domain, strategy, number of threads
		eval = evaluator.evaluate(state, pid, arguments[0]);
		state = eval.state;
		domain = eval.value;
		eval = evaluator.evaluate(state, pid, arguments[1]);
		state = eval.state;
		strategy = eval.value;
		eval = evaluator.evaluate(state, pid, arguments[2]);
		state = eval.state;
		nthreads = eval.value;
		// TODO: strategy should always be a concrete value ?
		assert strategy instanceof NumericExpression : call.getSource()
				+ ": stratey must be a numeric type";
		strategyNum = reasoner.extractNumber((NumericExpression) strategy);
		assert strategyNum instanceof IntegerNumber : arguments[1].getSource()
				+ ": strategy must be a DECOMP_STRATEGY type";
		strategyInt = ((IntegerNumber) strategyNum).intValue();
		switch (strategyInt) {
		case ModelConfiguration.DECOMP_ALL:
			LibdomainEvaluator libevaluator = (LibdomainEvaluator) this.libEvaluatorLoader
					.getLibraryEvaluator(name, evaluator, modelFactory,
							symbolicUtil, symbolicAnalyzer);
			List<SymbolicExpression> subDecomp;
			SymbolicExpression[] argValues = new SymbolicExpression[3];

			Arrays.asList(domain, strategy, nthreads).toArray(argValues);
			subDecomp = libevaluator.evaluateDomDecompAllPartition(state, pid,
					process, arguments, argValues, call.getSource());
			statements.addAll(this.allDecompStatements(call, arguments[0]
					.expressionScope(), call.lhs().getExpressionType(),
					subDecomp, arguments[0].getSource()));
			break;
		case ModelConfiguration.DECOMP_ROUND_ROBIN:
			return super.enabledTransitions(state, call, pathCondition, pid,
					processIdentifier, atomicLockAction);
		case ModelConfiguration.DECOMP_RANDOM:
		default:
			throw new CIVLUnimplementedFeatureException("domain strategy");
		}
		for (int i = 0; i < statements.size(); i++) {
			transitions.add(Semantics.newTransition(pathCondition, pid,
					processIdentifier, statements.get(i), atomicLockAction));
		}
		return transitions;
	}

	private List<AssignStatement> allDecompStatements(
			CallOrSpawnStatement call, Scope exprScope, CIVLType exprType,
			List<SymbolicExpression> subDecomp, CIVLSource sourceOfLocation) {
		StructOrUnionLiteralExpression decompsConstantExpr;
		List<AssignStatement> assignStatements = new LinkedList<>();

		for (int i = 0; i < subDecomp.size(); i++) {
			SymbolicExpression decomp = subDecomp.get(i);
			AssignStatement assignStatement;

			decompsConstantExpr = modelFactory.structOrUnionLiteralExpression(
					sourceOfLocation, exprScope, exprType, decomp);
			assignStatement = modelFactory.assignStatement(call.getSource(),
					null, call.lhs(), decompsConstantExpr, false);
			assignStatement.setTargetTemp(call.target());
			assignStatements.add(assignStatement);
			assignStatement.source().removeOutgoing(assignStatement);
		}
		return assignStatements;
	}
}
