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
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayIndexExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrowExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.ArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.PointerType;
import edu.udel.cis.vsl.civl.model.IF.type.PrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.StructType;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.util.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.util.CIVLException.ErrorKind;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
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
	private String pidPrefix = "PID_";
	private String scopePrefix = "Scope_";
	private SymbolicTupleType processType;
	private SymbolicTupleType scopeType;

	/**
	 * An evaluator is used to evaluate expressions.
	 * 
	 * @param symbolicUniverse
	 *            The symbolic universe for the expressions.
	 */
	public Evaluator(SymbolicUniverse symbolicUniverse, ErrorLog log) {
		List<SymbolicType> scopeTypeList = new Vector<SymbolicType>();
		List<SymbolicType> pointerComponents = new Vector<SymbolicType>();
		List<SymbolicType> processTypeList = new Vector<SymbolicType>();

		this.symbolicUniverse = symbolicUniverse;
		processTypeList.add(symbolicUniverse.integerType());
		processType = symbolicUniverse.tupleType(
				symbolicUniverse.stringObject("process"), processTypeList);
		scopeTypeList.add(symbolicUniverse.integerType());
		scopeType = symbolicUniverse.tupleType(
				symbolicUniverse.stringObject("scope"), scopeTypeList);
		pointerComponents.add(scopeType);
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
		} else if (expression instanceof ArrowExpression) {
			result = evaluate(state, pid, (ArrowExpression) expression);
		} else if (expression instanceof BinaryExpression) {
			result = evaluate(state, pid, (BinaryExpression) expression);
		} else if (expression instanceof BooleanLiteralExpression) {
			result = evaluate(state, pid, (BooleanLiteralExpression) expression);
		} else if (expression instanceof ConditionalExpression) {
			result = evaluate(state, pid, (ConditionalExpression) expression);
		} else if (expression instanceof CastExpression) {
			result = evaluate(state, pid, (CastExpression) expression);
		} else if (expression instanceof DotExpression) {
			result = evaluate(state, pid, (DotExpression) expression);
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
		} else if (expression instanceof SelfExpression) {
			result = evaluate(state, pid, (SelfExpression) expression);
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
	 * Evaluate a reference to a struct field.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The dot expression.
	 * @return The symbolic expression for reading the struct field.
	 */
	public SymbolicExpression evaluate(State state, int pid,
			DotExpression expression) {
		SymbolicExpression currentValue = evaluate(state, pid,
				expression.struct());
		Variable structVariable = getVariable(state, pid, expression.struct());
		Identifier field = expression.field();
		StructType structType;
		IntObject index = null;
		SymbolicExpression result;

		assert structVariable.type() instanceof StructType;
		structType = (StructType) structVariable.type();
		for (int i = 0; i < structType.fields().size(); i++) {
			if (structType.fields().get(i).name().equals(field)) {
				index = symbolicUniverse.intObject(i);
				break;
			}
		}
		assert index != null;
		result = symbolicUniverse.tupleRead(currentValue, index);
		return result;
	}

	/**
	 * Evaluate a reference to a struct pointer field.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The arrow expression.
	 * @return The symbolic expression for reading the struct field.
	 */
	public SymbolicExpression evaluate(State state, int pid,
			ArrowExpression expression) {
		SymbolicExpression pointerValue = evaluate(state, pid,
				expression.structPointer());
		Variable structVariable = getVariable(state, pid,
				expression.structPointer());
		Identifier field = expression.field();
		StructType structType;
		IntObject index = null;
		SymbolicExpression result;
		SymbolicExpression currentValue;
		int scopeID;
		int variableID;

		assert structVariable.type() instanceof PointerType;
		assert ((PointerType) (structVariable.type())).baseType() instanceof StructType;
		structType = (StructType) ((PointerType) structVariable.type())
				.baseType();
		// structType = (StructType) structVariable.type();
		for (int i = 0; i < structType.fields().size(); i++) {
			if (structType.fields().get(i).name().equals(field)) {
				index = symbolicUniverse.intObject(i);
				break;
			}
		}
		assert index != null;
		scopeID = getPointerTargetScope(state, pid, pointerValue);
		variableID = getPointerTargetVariableID(state, pid, pointerValue);
		// TODO: Traverse offsets if necessary
		currentValue = state.getScope(scopeID).getValue(variableID);
		result = symbolicUniverse.tupleRead(currentValue, index);
		return result;
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

	public SymbolicExpression evaluate(State state, int pid,
			SelfExpression expression) {
		return symbolicUniverse.symbolicConstant(
				symbolicUniverse.stringObject(pidPrefix + pid), processType);
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

		components.add(symbolicUniverse.symbolicConstant(
				symbolicUniverse.stringObject(scopePrefix + scope), scopeType));
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
		} else if (target instanceof UnaryExpression
				&& ((UnaryExpression) target).operator() == UNARY_OPERATOR.ADDRESSOF) {
			result = pointerTarget(((UnaryExpression) target).operand());
		}
		assert result != null;
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
		SymbolicObject scope;
		String scopeIDString;
		Number variableNumber;
		int scopeID;
		int variableID;
		SymbolicExpression value;

		assert pointer.type().equals(pointerType);
		assert pointer.numArguments() == 1;
		assert pointer.argument(0) instanceof SymbolicSequence;
		assert ((SymbolicSequence<?>) pointer.argument(0)).size() == 3;
		pointerTuple = (SymbolicSequence<?>) pointer.argument(0);
		scope = (SymbolicObject) pointerTuple.get(0);
		scopeIDString = scope.toString();
		scopeID = Integer.parseInt(scopeIDString.split("_")[1]);
		variableNumber = symbolicUniverse
				.extractNumber((NumericExpression) pointerTuple.get(1));
		variableID = ((IntegerNumber) variableNumber).intValue();
		value = state.getScope(scopeID).getValue(variableID);
		result = navigateReference(state, pid, value,
				(SymbolicExpression) pointerTuple.get(2));
		assert result != null;
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
			return symbolicUniverse.nullExpression();
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
		if (expression instanceof VariableExpression) {
			return ((VariableExpression) expression).variable();
		} else if (expression instanceof ArrayIndexExpression) {
			return baseArray(state, pid, (ArrayIndexExpression) expression);
		} else if (expression instanceof UnaryExpression) {
			SymbolicExpression pointer;
			SymbolicSequence<?> pointerTuple;
			SymbolicObject scope;
			String scopeIDString;
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
				scope = (SymbolicObject) pointerTuple.get(0);
				scopeIDString = scope.toString();
				scopeID = Integer.parseInt(scopeIDString.split("_")[1]);
				variableNumber = symbolicUniverse
						.extractNumber((NumericExpression) pointerTuple.get(1));
				//scopeID = ((IntegerNumber) scopeNumber).intValue();
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

	/**
	 * Evaluate an expression that returns a variable, and get the ID of the
	 * dynamic scope containing that variable.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The expression for the variable.
	 * @return The id of the scope containing the variable.
	 */
	public int getVariableScopeID(State state, int pid, Expression expression) {
		SymbolicExpression value = evaluate(state, pid, expression);
		Variable variable = getVariable(state, pid, expression);

		if (value.type().equals(pointerType)) {
			return getPointerTargetScope(state, pid, value);
		} else {
			return state.getScopeId(pid, variable);
		}
	}

	int getPointerTargetScope(State state, int pid, Expression expression) {
		SymbolicExpression pointer;
		SymbolicSequence<?> pointerTuple;
		SymbolicObject scope;
		String scopeIDString;
		int scopeID;

		assert ((UnaryExpression) expression).operator() == UNARY_OPERATOR.DEREFERENCE;
		pointer = evaluate(state, pid, ((UnaryExpression) expression).operand());
		assert pointer.type().equals(pointerType);
		assert pointer.numArguments() == 1;
		assert pointer.argument(0) instanceof SymbolicSequence;
		assert ((SymbolicSequence<?>) pointer.argument(0)).size() == 3;
		pointerTuple = (SymbolicSequence<?>) pointer.argument(0);
		scope = (SymbolicObject) pointerTuple.get(0);
		scopeIDString = scope.toString();
		scopeID = Integer.parseInt(scopeIDString.split("_")[1]);
		return scopeID;
	}

	int getPointerTargetScope(State state, int pid, SymbolicExpression pointer) {
		SymbolicSequence<?> pointerTuple;
		SymbolicObject scope;
		String scopeIDString;
		int scopeID;
	
		assert pointer.type().equals(pointerType);
		assert pointer.numArguments() == 1;
		assert pointer.argument(0) instanceof SymbolicSequence;
		assert ((SymbolicSequence<?>) pointer.argument(0)).size() == 3;
		pointerTuple = (SymbolicSequence<?>) pointer.argument(0);
		scope = (SymbolicObject) pointerTuple.get(0);
		scopeIDString = scope.toString();
		scopeID = Integer.parseInt(scopeIDString.split("_")[1]);
		return scopeID;
	}

	int getPointerTargetVariableID(State state, int pid,
			SymbolicExpression pointer) {
		SymbolicSequence<?> pointerTuple;
		Number scopeNumber;
		int scopeID;

		assert pointer.type().equals(pointerType);
		assert pointer.numArguments() == 1;
		assert pointer.argument(0) instanceof SymbolicSequence;
		assert ((SymbolicSequence<?>) pointer.argument(0)).size() == 3;
		pointerTuple = (SymbolicSequence<?>) pointer.argument(0);
		scopeNumber = symbolicUniverse
				.extractNumber((NumericExpression) pointerTuple.get(1));
		scopeID = ((IntegerNumber) scopeNumber).intValue();
		return scopeID;
	}

	/**
	 * Get the variable at the base of a (possibly multi-dimensional) array.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The array index expression.
	 * @return The variable corresponding to the base of this array.
	 */
	private Variable baseArray(State state, int pid,
			ArrayIndexExpression expression) {
		if (expression.array() instanceof ArrayIndexExpression) {
			return baseArray(state, pid,
					((ArrayIndexExpression) expression.array()));
		} else if (expression.array() instanceof VariableExpression) {
			return ((VariableExpression) expression.array()).variable();
		} else if (expression.array() instanceof ArrowExpression) {
			return getVariable(state, pid,
					((ArrowExpression) expression.array()).structPointer());
		} else if (expression.array() instanceof DotExpression) {
			return getVariable(state, pid,
					((DotExpression) expression.array()).struct());
		}
		return null;
	}

	SymbolicType pointerType() {
		return pointerType;
	}

}
