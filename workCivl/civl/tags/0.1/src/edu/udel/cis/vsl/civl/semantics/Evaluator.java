/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.List;
import java.util.Vector;

import edu.udel.cis.vsl.civl.log.ErrorLog;
import edu.udel.cis.vsl.civl.log.ExecutionException;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayIndexExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.ArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.PointerType;
import edu.udel.cis.vsl.civl.model.IF.type.PrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.DynamicScope;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.util.ExecutionProblem.Certainty;
import edu.udel.cis.vsl.civl.util.ExecutionProblem.ErrorKind;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;
import edu.udel.cis.vsl.sarl.number.real.RealNumberFactory;

/**
 * An evaluator is used to evaluate expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class Evaluator {

	private SymbolicUniverse symbolicUniverse;
	private RealNumberFactory numberFactory = new RealNumberFactory();
	private SymbolicTupleType pointerType;
	private ErrorLog log;

	/**
	 * An evaluator is used to evaluate expressions.
	 * 
	 * @param symbolicUniverse
	 *            The symbolic universe for the expressions.
	 */
	public Evaluator(SymbolicUniverse symbolicUniverse, ErrorLog log) {
		List<SymbolicType> pointerComponents = new Vector<SymbolicType>();

		this.symbolicUniverse = symbolicUniverse;
		pointerComponents.add(symbolicUniverse.integerType());
		pointerComponents.add(symbolicUniverse.integerType());
		pointerComponents.add(symbolicUniverse.arrayType(symbolicUniverse
				.integerType()));
		pointerType = symbolicUniverse.tupleType(
				symbolicUniverse.stringObject("pointer"), pointerComponents);
		this.log = log;
	}

	public ErrorLog log() {
		return log;
	}

	/**
	 * Evaluate a generic expression. One of the overloaded evaluate methods for
	 * specific expressions should always be used instead.
	 */
	public SymbolicExpression evaluate(State state, int pid,
			Expression expression) {
		SymbolicExpression result = null;

		if (expression instanceof ArrayIndexExpression) {
			result = evaluate(state, pid, (ArrayIndexExpression) expression);
		} else if (expression instanceof BinaryExpression) {
			result = evaluate(state, pid, (BinaryExpression) expression);
		} else if (expression instanceof BooleanLiteralExpression) {
			result = evaluate(state, pid, (BooleanLiteralExpression) expression);
		} else if (expression instanceof ConditionalExpression) {
			result = evaluate(state, pid, (ConditionalExpression) expression);
		} else if (expression instanceof CastExpression) {
			result = evaluate(state, pid, (CastExpression) expression);
		} else if (expression instanceof IntegerLiteralExpression) {
			result = evaluate(state, pid, (IntegerLiteralExpression) expression);
		} else if (expression instanceof RealLiteralExpression) {
			result = evaluate(state, pid, (RealLiteralExpression) expression);
		} else if (expression instanceof StringLiteralExpression) {
			result = evaluate(state, pid, (StringLiteralExpression) expression);
		} else if (expression instanceof UnaryExpression) {
			result = evaluate(state, pid, (UnaryExpression) expression);
		} else if (expression instanceof VariableExpression) {
			result = evaluate(state, pid, (VariableExpression) expression);
		}
		if (result != null) {
			result = (SymbolicExpression) symbolicUniverse.canonic(result);
		}
		return result;
	}

	/**
	 * Evaluate a conditional expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            the pid of the currently executing process.
	 * @param expression
	 *            The conditional expression.
	 * @return A symbolic expression for the result of the conditional.
	 */
	public SymbolicExpression evaluate(State state, int pid,
			ConditionalExpression expression) {
		SymbolicExpression condition = evaluate(state, pid,
				expression.getCondition());
		SymbolicExpression trueBranch = evaluate(state, pid,
				expression.getTrueBranch());
		SymbolicExpression falseBranch = evaluate(state, pid,
				expression.getFalseBranch());

		assert condition instanceof BooleanExpression;
		return symbolicUniverse.cond((BooleanExpression) condition, trueBranch,
				falseBranch);
	}

	/**
	 * Evaluate an array index expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The array index expression.
	 * @return A symbolic expression for an array read.
	 */
	public SymbolicExpression evaluate(State state, int pid,
			ArrayIndexExpression expression) {
		SymbolicExpression array = evaluate(state, pid, expression.array());
		SymbolicExpression index = evaluate(state, pid, expression.index());

		while (array.type().equals(pointerType)) {
			array = dereference(state, pid, array);
		}
		// TODO: simplify index?
		return symbolicUniverse.arrayRead(array, (NumericExpression) index);
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
	 */
	public SymbolicExpression evaluate(State state, int pid,
			BinaryExpression expression) {
		SymbolicExpression left = evaluate(state, pid, expression.left());
		SymbolicExpression right = evaluate(state, pid, expression.right());

		// TODO: Check all expression types.
		switch (expression.operator()) {
		case PLUS:
			return symbolicUniverse.add((NumericExpression) left,
					(NumericExpression) right);
		case MINUS:
			return symbolicUniverse.subtract((NumericExpression) left,
					(NumericExpression) right);
		case TIMES:
			return symbolicUniverse.multiply((NumericExpression) left,
					(NumericExpression) right);
		case DIVIDE:
			return symbolicUniverse.divide((NumericExpression) left,
					(NumericExpression) right);
		case LESS_THAN:
			return symbolicUniverse.lessThan((NumericExpression) left,
					(NumericExpression) right);
		case LESS_THAN_EQUAL:
			return symbolicUniverse.lessThanEquals((NumericExpression) left,
					(NumericExpression) right);
		case EQUAL:
			return symbolicUniverse.equals(left, right);
		case NOT_EQUAL:
			return symbolicUniverse.not(symbolicUniverse.equals(left, right));
		case AND:
			return symbolicUniverse.and((BooleanExpression) left,
					(BooleanExpression) right);
		case OR:
			return symbolicUniverse.or((BooleanExpression) left,
					(BooleanExpression) right);
		case MODULO:
			return symbolicUniverse.modulo((NumericExpression) left,
					(NumericExpression) right);
		}
		return null;
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
	public SymbolicExpression evaluate(State state, int pid,
			BooleanLiteralExpression expression) {
		return symbolicUniverse.bool(expression.value());
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
	 */
	public SymbolicExpression evaluate(State state, int pid,
			CastExpression expression) {
		SymbolicExpression uncastExpression = evaluate(state, pid,
				expression.getExpression());
		Type castType = expression.getCastType();
		SymbolicType symbolicType = symbolicType(castType);
		SymbolicExpression result;

		if (castType == null) {
			log.report(new ExecutionException(ErrorKind.OTHER,
					Certainty.CONCRETE, "Unable to perform cast : "
							+ expression + ".  Not implemented."));
		}
		result = symbolicUniverse.cast(symbolicType, uncastExpression);
		return result;
	}

	private SymbolicType symbolicType(Type type) {
		SymbolicType result = null;
		if (type instanceof PrimitiveType) {
			switch (((PrimitiveType) type).primitiveType()) {
			case BOOL:
				result = symbolicUniverse.booleanType();
				break;
			case INT:
				result = symbolicUniverse.integerType();
				break;
			case REAL:
				result = symbolicUniverse.realType();
				break;
			case STRING:

			default:
				result = null;

			}
		} else if (type instanceof ArrayType) {
			result = symbolicUniverse.arrayType(symbolicType(((ArrayType) type)
					.baseType()));
		}
		return result;
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
	public SymbolicExpression evaluate(State state, int pid,
			IntegerLiteralExpression expression) {
		return symbolicUniverse.integer(expression.value().intValue());
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
	public SymbolicExpression evaluate(State state, int pid,
			RealLiteralExpression expression) {
		return symbolicUniverse.number(symbolicUniverse
				.numberObject(numberFactory.rational(expression.value()
						.toPlainString())));
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
	public SymbolicExpression evaluate(State state, int pid,
			StringLiteralExpression expression) {
		// StringObject result =
		// symbolicUniverse.stringObject(expression.value());
		// TODO: Figure this out.
		// Right now, strings are intercepted in the executor.
		// They are used in write statements, and are
		// just passed to the PrintStream.
		return null;
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
	 */
	public SymbolicExpression evaluate(State state, int pid,
			UnaryExpression expression) {
		switch (expression.operator()) {
		case NEGATIVE:
			return symbolicUniverse.minus((NumericExpression) evaluate(state,
					pid, expression.operand()));
		case NOT:
			return symbolicUniverse.not((BooleanExpression) evaluate(state,
					pid, expression.operand()));
		case ADDRESSOF:
			return reference(state, pid, expression.operand());
		case DEREFERENCE:
			return dereference(state, pid, expression.operand());
		}
		return null;
	}

	SymbolicExpression reference(State state, int pid, Expression operand) {
		SymbolicExpression result = null;
		List<SymbolicExpression> navigationSequence = navigationSequence(state,
				pid, operand);
		List<SymbolicExpression> components = new Vector<SymbolicExpression>();
		Variable variable = pointerTarget(operand);
		int scope = state.getScopeId(pid, variable);

		components.add(symbolicUniverse.integer(scope));
		components.add(symbolicUniverse.integer(variable.vid()));
		components.add(symbolicUniverse.array(symbolicUniverse.integerType(),
				navigationSequence));
		result = symbolicUniverse.tuple(pointerType, components);
		return result;
	}

	private Variable pointerTarget(Expression target) {
		Variable result = null;

		if (target instanceof VariableExpression) {
			result = ((VariableExpression) target).variable();
		} else if (target instanceof ArrayIndexExpression) {
			result = pointerTarget(((ArrayIndexExpression) target).array());
		}
		return result;
	}

	private List<SymbolicExpression> navigationSequence(State state, int pid,
			Expression operand) {
		List<SymbolicExpression> result = new Vector<SymbolicExpression>();

		// TODO: Variable expressions return empty sequence, but need to error
		// check otherwise.
		if (operand instanceof ArrayIndexExpression) {
			result.addAll(navigationSequence(state, pid,
					((ArrayIndexExpression) operand).array()));
			result.add(evaluate(state, pid,
					((ArrayIndexExpression) operand).index()));
		}
		return result;
	}

	private SymbolicExpression dereference(State state, int pid,
			Expression operand) {
		SymbolicExpression pointer = evaluate(state, pid, operand);
		return dereference(state, pid, pointer);
	}

	SymbolicExpression dereference(State state, int pid,
			SymbolicExpression pointer) {
		SymbolicExpression result = null;
		SymbolicSequence<?> pointerTuple;
		Number scopeNumber;
		Number variableNumber;
		int scopeID;
		int variableID;
		SymbolicExpression value;

		assert pointer.type().equals(pointerType);
		assert pointer.numArguments() == 1;
		assert pointer.argument(0) instanceof SymbolicSequence;
		assert ((SymbolicSequence<?>) pointer.argument(0)).size() == 3;
		pointerTuple = (SymbolicSequence<?>) pointer.argument(0);
		scopeNumber = symbolicUniverse
				.extractNumber((NumericExpression) pointerTuple.get(0));
		variableNumber = symbolicUniverse
				.extractNumber((NumericExpression) pointerTuple.get(1));
		scopeID = ((IntegerNumber) scopeNumber).intValue();
		variableID = ((IntegerNumber) variableNumber).intValue();
		value = state.getScope(scopeID).getValue(variableID);
		result = navigateReference(state, pid, value,
				(SymbolicExpression) pointerTuple.get(2));
		return result;
	}

	private SymbolicExpression navigateReference(State state, int pid,
			SymbolicExpression base, SymbolicExpression sequence) {
		SymbolicExpression result = base;
		SymbolicSequence<?> innerSequence;

		assert sequence.argument(0) instanceof SymbolicSequence;
		innerSequence = (SymbolicSequence<?>) sequence.argument(0);
		for (int i = 0; i < innerSequence.size(); i++) {
			NumericExpression argumentNumber;

			assert innerSequence.get(i) instanceof NumericExpression;
			argumentNumber = (NumericExpression) innerSequence.get(i);
			if (result.operator() == SymbolicOperator.DENSE_ARRAY_WRITE
					|| result.operator() == SymbolicOperator.ARRAY_WRITE) {
				result = symbolicUniverse.arrayRead(result, argumentNumber);
			}
			// TODO: handle otherwise
		}
		return result;
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
	 */
	public SymbolicExpression evaluate(State state, int pid,
			VariableExpression expression) {
		SymbolicExpression currentValue = state.valueOf(pid,
				expression.variable());

		if (currentValue == null) {
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
			PrintStream ps = new PrintStream(baos);

			state.print(ps);
			log.report(new ExecutionException(ErrorKind.UNDEFINED_VALUE,
					Certainty.PROVEABLE,
					"Attempt to read unitialized variable: "
							+ expression.variable() + "\n\n" + baos.toString()));
		}
		return symbolicUniverse.reasoner(
				(BooleanExpression) state.pathCondition()).simplify(
				currentValue);
	}

	/**
	 * Evaluate an expression that returns a variable. This method gets the
	 * actual variable, not the value stored in the variable. It is used for
	 * finding the correct location to perform a write.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The expression for the variable.
	 * @return The variable.
	 */
	public Variable getVariable(State state, int pid, Expression expression) {
		DynamicScope scope = state.getScope(state.process(pid).scope());

		if (expression instanceof VariableExpression) {
			return ((VariableExpression) expression).variable();
		} else if (expression instanceof ArrayIndexExpression) {
			return baseArray(scope, (ArrayIndexExpression) expression);
		} else if (expression instanceof UnaryExpression) {
			SymbolicExpression pointer;
			SymbolicSequence<?> pointerTuple;
			Number scopeNumber;
			Number variableNumber;
			int scopeID;
			int variableID;
			Variable variable;

			assert ((UnaryExpression) expression).operator() == UNARY_OPERATOR.DEREFERENCE;
			pointer = evaluate(state, pid,
					((UnaryExpression) expression).operand());
			do {
				assert pointer.type().equals(pointerType);
				assert pointer.numArguments() == 1;
				assert pointer.argument(0) instanceof SymbolicSequence;
				assert ((SymbolicSequence<?>) pointer.argument(0)).size() == 3;
				pointerTuple = (SymbolicSequence<?>) pointer.argument(0);
				scopeNumber = symbolicUniverse
						.extractNumber((NumericExpression) pointerTuple.get(0));
				variableNumber = symbolicUniverse
						.extractNumber((NumericExpression) pointerTuple.get(1));
				scopeID = ((IntegerNumber) scopeNumber).intValue();
				variableID = ((IntegerNumber) variableNumber).intValue();
				variable = state.getScope(scopeID).lexicalScope()
						.getVariable(variableID);
				pointer = state.getScope(scopeID).getValue(variableID);
			} while (variable.type() instanceof PointerType);
			return variable;

		}
		throw new RuntimeException("Retrieving variable from " + expression
				+ " not implemented.");
	}

	int getPointerTargetScope(State state, int pid, Expression expression) {
		SymbolicExpression pointer;
		SymbolicSequence<?> pointerTuple;
		Number scopeNumber;
		int scopeID;

		assert ((UnaryExpression) expression).operator() == UNARY_OPERATOR.DEREFERENCE;
		pointer = evaluate(state, pid, ((UnaryExpression) expression).operand());
		assert pointer.type().equals(pointerType);
		assert pointer.numArguments() == 1;
		assert pointer.argument(0) instanceof SymbolicSequence;
		assert ((SymbolicSequence<?>) pointer.argument(0)).size() == 3;
		pointerTuple = (SymbolicSequence<?>) pointer.argument(0);
		scopeNumber = symbolicUniverse
				.extractNumber((NumericExpression) pointerTuple.get(0));
		scopeID = ((IntegerNumber) scopeNumber).intValue();
		return scopeID;
	}

	/**
	 * Get the variable at the base of a (possibly multi-dimensional) array.
	 * 
	 * @param scope
	 *            The dynamic scope containing this array reference.
	 * @param expression
	 *            The array index expression.
	 * @return The variable corresponding to the base of this array.
	 */
	private Variable baseArray(DynamicScope scope,
			ArrayIndexExpression expression) {
		if (expression.array() instanceof ArrayIndexExpression) {
			return baseArray(scope, ((ArrayIndexExpression) expression.array()));
		} else if (expression.array() instanceof VariableExpression) {
			return ((VariableExpression) expression.array()).variable();
		}
		return null;
	}

	SymbolicType pointerType() {
		return pointerType;
	}

}
