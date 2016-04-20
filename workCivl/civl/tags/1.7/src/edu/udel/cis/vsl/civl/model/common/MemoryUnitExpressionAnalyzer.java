package edu.udel.cis.vsl.civl.model.common;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.AbstractFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.MemoryUnitExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RegularRangeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ScopeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.SelfReference;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.DomainIteratorStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlParForSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * This implements the static analysis of impact and reachable memory units and
 * store the information with locations.
 * 
 * TODO check pointer and non-pointer conversion TODO side effects in abstract
 * functions get checked?
 * 
 * @author Manchun Zheng
 *
 */
public class MemoryUnitExpressionAnalyzer {

	/**
	 * The model factory to be used for constructing memory unit expressions.
	 */
	private ModelFactory modelFactory;

	MemoryUnitExpressionAnalyzer(ModelFactory modelFactory) {
		this.modelFactory = modelFactory;
	}

	/**
	 * Computes the impact/reachable memory units of a model.
	 * 
	 * @param model
	 *            The model to be analyzed.
	 */
	void memoryUnitAnalysis(Model model) {
		for (CIVLFunction function : model.functions()) {
			for (Location location : function.locations()) {
				computeReachableMemoryUnitsOfLocation(location);
				computeImpactMemoryUnitsOfLocation(location);
			}
		}
	}

	/**
	 * Computes the reachable memory units of a location, and puts them into to
	 * two sets, one with pointers and the other without pointers, because at
	 * runtime, only those with pointers need to be explored more for memory
	 * units pointed by them.
	 * 
	 * @param location
	 */
	private void computeReachableMemoryUnitsOfLocation(Location location) {
		Set<MemoryUnitExpression> reachableMemUnitsWoPointer = new HashSet<>();
		Set<MemoryUnitExpression> reachableMemUnitsWtPointer = new HashSet<>();
		Scope myScope = location.scope();
		SelfReference selfRef = modelFactory.selfReference();
		Set<Variable> writableVars = location.writableVariables();

		while (myScope != null) {
			int size = myScope.numVariables();
			int scopeID = myScope.id();

			for (int i = 0; i < size; i++) {
				// ignore heap variable
				if (i == ModelConfiguration.heapVariableIndex)
					continue;
				else {
					Variable variable = myScope.variable(i);
					MemoryUnitExpression memUnit;

					if ((scopeID == 0 && variable.name().name()
							.equals(ModelConfiguration.ATOMIC_LOCK_VARIABLE)))
						continue;
					memUnit = modelFactory.memoryUnitExpression(
							variable.getSource(), variable, variable.type(),
							selfRef, writableVars.contains(variable),
							variable.hasPointerRef());
					if (variable.hasPointerRef()
							&& !variable.type().isHandleType()) {
						reachableMemUnitsWtPointer.add(memUnit);
					} else
						reachableMemUnitsWoPointer.add(memUnit);
				}
			}
			myScope = myScope.parent();
		}
		location.setReachableMemUnitsWoPointer(reachableMemUnitsWoPointer);
		location.setReachableMemUnitsWtPointer(reachableMemUnitsWtPointer);
	}

	/**
	 * TODO is it necessary to distinguish memory units with pointer? TODO
	 * impact memory units are subset of reachable units
	 * 
	 * @param location
	 */
	private void computeImpactMemoryUnitsOfLocation(Location location) {
		Set<MemoryUnitExpression> impactMemUnits = new HashSet<>();
		Set<CallOrSpawnStatement> systemCalls = new HashSet<>();

		if (location.enterAtom() || location.enterAtomic()) {
			boolean predictable = computeImpactMemoryUnitsOfAtomicAndAtom(
					location.writableVariables(), location, impactMemUnits,
					systemCalls);
			if (predictable)
				location.setImpactMemoryUnit(impactMemUnits);
			else
				location.setImpactMemoryUnit(null);
		} else {
			for (Statement statement : location.outgoing()) {
				computeImpactMemoryUnitsOfStatement(
						location.writableVariables(), null, statement,
						impactMemUnits, systemCalls);
			}
			location.setImpactMemoryUnit(impactMemUnits);
		}
		location.setSystemCalls(systemCalls);
	}

	private boolean computeImpactMemoryUnitsOfAtomicAndAtom(
			Set<Variable> writableVars, Location location,
			Set<MemoryUnitExpression> impactMemUnits,
			Set<CallOrSpawnStatement> systemCalls) {
		int atomicCount = 0;

		if (location.enterAtom() || location.enterAtomic()) {
			Set<Integer> checkedLocations = new HashSet<Integer>();
			Stack<Location> workings = new Stack<Location>();

			workings.add(location);
			// DFS searching for reachable statements inside the $atomic/$atom
			// block
			while (!workings.isEmpty()) {
				Location currentLocation = workings.pop();

				checkedLocations.add(currentLocation.id());
				if (location.enterAtom() && currentLocation.enterAtom())
					atomicCount++;
				if (location.enterAtomic() && currentLocation.enterAtomic())
					atomicCount++;
				if (location.enterAtom() && currentLocation.leaveAtom())
					atomicCount--;
				if (location.enterAtomic() && currentLocation.leaveAtomic())
					atomicCount--;
				if (atomicCount == 0) {
					if (location.enterAtom() && !currentLocation.enterAtom())
						atomicCount++;
					if (location.enterAtomic()
							&& !currentLocation.enterAtomic())
						atomicCount++;
					continue;
				}
				for (Statement statement : currentLocation.outgoing()) {
					if (statement instanceof CallOrSpawnStatement) {
						CallOrSpawnStatement callOrSpawnStatement = (CallOrSpawnStatement) statement;

						if (callOrSpawnStatement.isCall()
								&& !callOrSpawnStatement.isSystemCall()) {
							impactMemUnits.clear();
							systemCalls.clear();
							return false;
						}
					}
					this.computeImpactMemoryUnitsOfStatement(writableVars,
							currentLocation.scope(), statement, impactMemUnits,
							systemCalls);
					if (statement.target() != null) {
						if (!checkedLocations.contains(statement.target().id())) {
							workings.push(statement.target());
						}
					}
				}
			}
		}
		return true;
	}

	/**
	 * Computes impact memory units of a statement, which looks at expressions
	 * appearing in the statement including its guard.
	 * 
	 * @param statement
	 * @param result
	 * @param systemCalls
	 */
	private void computeImpactMemoryUnitsOfStatement(
			Set<Variable> writableVars, Scope currentScope,
			Statement statement, Set<MemoryUnitExpression> result,
			Set<CallOrSpawnStatement> systemCalls) {
		StatementKind statementKind = statement.statementKind();

		// computes impact memory of guard
		computeImpactMemoryUnitsOfExpression(writableVars, statement.guard(),
				result);
		switch (statementKind) {
		// case ASSERT: {
		// AssertStatement assertStatement = (AssertStatement) statement;
		// Expression[] explanation = assertStatement.getExplanation();
		//
		// computeImpactMemoryUnitsOfExpression(writableVars,
		// assertStatement.getCondition(), result);
		// if (explanation != null)
		// for (Expression arg : explanation)
		// computeImpactMemoryUnitsOfExpression(writableVars, arg,
		// result);
		// break;
		// }
		case ASSIGN: {
			AssignStatement assignStatement = (AssignStatement) statement;

			if (!assignStatement.isInitialization())
				computeImpactMemoryUnitsOfExpression(writableVars,
						assignStatement.getLhs(), result);
			computeImpactMemoryUnitsOfExpression(writableVars,
					assignStatement.rhs(), result);
			break;
		}
		// case ASSUME:
		// computeImpactMemoryUnitsOfExpression(writableVars,
		// ((AssumeStatement) statement).getExpression(), result);
		// break;
		case CALL_OR_SPAWN: {
			CallOrSpawnStatement call = (CallOrSpawnStatement) statement;

			if (call.isSystemCall()) {
				if (currentScope != null
						&& isLowerThan(statement.lowestScope(), currentScope))
					break;
				systemCalls.add(call);
			}
			for (Expression argument : call.arguments())
				computeImpactMemoryUnitsOfExpression(writableVars, argument,
						result);
			break;
		}
		case DOMAIN_ITERATOR:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((DomainIteratorStatement) statement).domain(), result);
			break;
		case CIVL_PAR_FOR_ENTER:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((CivlParForSpawnStatement) statement).domain(), result);
			break;
		case MALLOC: {
			MallocStatement mallocStatement = (MallocStatement) statement;

			computeImpactMemoryUnitsOfExpression(writableVars,
					mallocStatement.getLHS(), result);
			computeImpactMemoryUnitsOfExpression(writableVars,
					mallocStatement.getScopeExpression(), result);
			computeImpactMemoryUnitsOfExpression(writableVars,
					mallocStatement.getSizeExpression(), result);
			break;
		}
		case NOOP:
			break;
		case CONTRACT:
			break;// TODO: if in the future, there are contracts for shared
					// storage, this cannot be no operation
		case RETURN: {
			ReturnStatement returnStatement = (ReturnStatement) statement;

			if (returnStatement.expression() != null)
				computeImpactMemoryUnitsOfExpression(writableVars,
						returnStatement.expression(), result);
			break;
		}
		default:
			throw new CIVLUnimplementedFeatureException(
					"computing the impact memory units" + " of statements of "
							+ statementKind + " kind");
		}

	}

	private void computeImpactMemoryUnitsOfExpression(
			Set<Variable> writableVars, Expression expression,
			Set<MemoryUnitExpression> result) {
		this.computeImpactMemoryUnitsOfExpression(writableVars, expression, result, 0);
	}

	private boolean isLowerThan(Scope s0, Scope s1) {
		if (s0 == null || s1 == null)
			return false;
		else {
			Scope parent0 = s0, parent1 = s1;

			while (parent0.id() != 0 && parent1.id() != 0) {
				if (parent0.id() == s1.id())
					return true;
				if (parent1.id() == s0.id())
					return false;
				parent0 = parent0.parent();
				parent1 = parent1.parent();
			}
			if (parent0.id() == 0)
				return false;
		}
		return true;
	}

	/**
	 * Computes the impact memory unit of an expression.
	 * 
	 * @param expression
	 * @param result
	 */
	private void computeImpactMemoryUnitsOfExpression(
			Set<Variable> writableVars, Expression expression,
			Set<MemoryUnitExpression> result, int derefCount) {
		ExpressionKind expressionKind = expression.expressionKind();

		switch (expressionKind) {
		case ABSTRACT_FUNCTION_CALL:
			for (Expression arg : ((AbstractFunctionCallExpression) expression)
					.arguments()) {
				computeImpactMemoryUnitsOfExpression(writableVars, arg, result,
						derefCount);
			}
			break;
		case ADDRESS_OF:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((AddressOfExpression) expression).operand(), result,
					derefCount);
			break;
		case ARRAY_LITERAL: {
			Expression[] elements = ((ArrayLiteralExpression) expression)
					.elements();

			for (Expression element : elements) {
				computeImpactMemoryUnitsOfExpression(writableVars, element,
						result, derefCount);
			}
			break;
		}
		case BINARY: {
			BinaryExpression binaryExpression = (BinaryExpression) expression;

			computeImpactMemoryUnitsOfExpression(writableVars,
					binaryExpression.left(), result, derefCount);
			computeImpactMemoryUnitsOfExpression(writableVars,
					binaryExpression.right(), result, derefCount);
			break;
		}
		case BOOLEAN_LITERAL:
			break;
		case BOUND_VARIABLE:
			// A bound variable only appears in quantifier expressions such as
			// $forall (i=0 .. 10) f(i)=10*i, and it disappears after the
			// expression so it won't affect the POR.
			break;
		case CAST:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((CastExpression) expression).getExpression(), result,
					derefCount);
			break;
		case CHAR_LITERAL:
			break;
		case COND:
			throw new CIVLInternalException(
					"Encounter conditional expression in "
							+ "memory unit analyzer which should already been translated away in the "
							+ "model translator", expression.getSource());
		case DEREFERENCE:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((DereferenceExpression) expression).pointer(), result,
					derefCount + 1);
			break;
		case DERIVATIVE:// TODO check if its arguments should be checked
			break;
		case DOMAIN_GUARD:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((DomainGuardExpression) expression).domain(), result,
					derefCount);
			break;
		case DOT:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((DotExpression) expression).structOrUnion(), result,
					derefCount);
			break;
		case DYNAMIC_TYPE_OF:
			break;
		case FUNCTION_IDENTIFIER:// TODO clean it up
			break;
		case FUNCTION_GUARD:
			break;
		case INITIAL_VALUE:
			break;
		case INTEGER_LITERAL:
			break;
		case MEMORY_UNIT:
			break;
		case NULL_LITERAL:
			break;
		case QUANTIFIER:// TODO implement it
			break;
		case REAL_LITERAL:
			break;
		case REC_DOMAIN_LITERAL: {
			RecDomainLiteralExpression domain = (RecDomainLiteralExpression) expression;
			int dim = domain.dimension();

			for (int i = 0; i < dim; i++)
				computeImpactMemoryUnitsOfExpression(writableVars,
						domain.rangeAt(i), result, derefCount);
			break;
		}
		case REGULAR_RANGE: {
			RegularRangeExpression rangeExpr = (RegularRangeExpression) expression;

			computeImpactMemoryUnitsOfExpression(writableVars,
					rangeExpr.getLow(), result, derefCount);
			computeImpactMemoryUnitsOfExpression(writableVars,
					rangeExpr.getHigh(), result, derefCount);
			computeImpactMemoryUnitsOfExpression(writableVars,
					rangeExpr.getStep(), result, derefCount);
			break;
		}
		case RESULT:
			break;
		case SCOPEOF:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((ScopeofExpression) expression).argument(), result,
					derefCount);
			break;
		case SELF:
			break;
		case SIZEOF_TYPE:
			break;
		case SIZEOF_EXPRESSION:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((SizeofExpression) expression).getArgument(), result,
					derefCount);
			break;
		case STRING_LITERAL:
			break;
		case STRUCT_OR_UNION_LITERAL: {
			Expression[] fields = ((StructOrUnionLiteralExpression) expression)
					.fields();

			for (Expression field : fields) {
				computeImpactMemoryUnitsOfExpression(writableVars, field,
						result, derefCount);
			}
		}
			break;
		case SUBSCRIPT:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((SubscriptExpression) expression).array(), result,
					derefCount);
			computeImpactMemoryUnitsOfExpression(writableVars,
					((SubscriptExpression) expression).index(), result,
					derefCount);

			break;
		case SYSTEM_GUARD:
			break;
		case UNARY:
			computeImpactMemoryUnitsOfExpression(writableVars,
					((UnaryExpression) expression).operand(), result,
					derefCount);
			break;
		case UNDEFINED_PROC:
			break;
		case VARIABLE: {
			Variable variable = ((VariableExpression) expression).variable();

			if (!((variable.scope().id() == 0 && variable.name().name()
					.equals(ModelConfiguration.ATOMIC_LOCK_VARIABLE)) || variable
					.type().isHandleType())) {
				boolean deref = false;

				if (derefCount > 0) {
					deref = true;
					derefCount--;
				}
				result.add(this.modelFactory.memoryUnitExpression(
						variable.getSource(), variable, variable.type(),
						modelFactory.selfReference(),
						writableVars.contains(variable), deref));
			}
			break;
		}
		case HERE_OR_ROOT:
			break;
		case PROC_NULL:
			break;
		case SYSTEM_FUNC_CALL:// TODO check
			break;
		case REMOTE_REFERENCE:// TODO: currently remote reference only allows
								// reading
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"computing the impact memory units" + " of expressions of "
							+ expressionKind + " kind");
		}

	}
}
