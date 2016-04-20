/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayIndexExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ResultExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ForkStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.JoinStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.ArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.HeapType;
import edu.udel.cis.vsl.civl.model.IF.type.PointerType;
import edu.udel.cis.vsl.civl.model.IF.type.PrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.PrimitiveType.PRIMITIVE_TYPE;
import edu.udel.cis.vsl.civl.model.IF.type.ProcessType;
import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.civl.model.IF.type.StructType;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.expression.CommonArrayIndexExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonBinaryExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonBooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonCastExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonConditionalExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonIntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRealLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonResultExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSelfExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonStringLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonUnaryExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonVariableExpression;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssertStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssignStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssumeStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCallStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonChooseStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonForkStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonJoinStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonNoopStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonReturnStatement;
import edu.udel.cis.vsl.civl.model.common.type.CommonArrayType;
import edu.udel.cis.vsl.civl.model.common.type.CommonHeapType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPointerType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPrimitiveType;
import edu.udel.cis.vsl.civl.model.common.type.CommonProcessType;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructField;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructType;
import edu.udel.cis.vsl.civl.model.common.variable.CommonVariable;

/**
 * The factory to create all model components. Usually this is the only way
 * model components will be created.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonModelFactory implements ModelFactory {

	/* Keep a unique number to identify locations. */
	private int locationID = 0;
	/* Keep a set of used identifiers for fly-weighting purposes. */
	private Map<String, Identifier> identifiers;
	/* Make one of each primitive type. */
	private PrimitiveType integerType = new CommonPrimitiveType(
			PRIMITIVE_TYPE.INT);
	private PrimitiveType booleanType = new CommonPrimitiveType(
			PRIMITIVE_TYPE.BOOL);
	private PrimitiveType realType = new CommonPrimitiveType(
			PRIMITIVE_TYPE.REAL);
	private PrimitiveType stringType = new CommonPrimitiveType(
			PRIMITIVE_TYPE.STRING);
	private HeapType heapType = new CommonHeapType();
	private ProcessType processType = new CommonProcessType();
	/* Make one canonical true and false. */
	private BooleanLiteralExpression trueExpression = new CommonBooleanLiteralExpression(
			true);
	private BooleanLiteralExpression falseExpression = new CommonBooleanLiteralExpression(
			false);
	/* Keep a unique number to identify scopes. */
	private int scopeID = 0;
	private int chooseID = 0;

	/**
	 * The factory to create all model components. Usually this is the only way
	 * model components will be created.
	 */
	public CommonModelFactory() {
		identifiers = new HashMap<String, Identifier>();
	}

	/**
	 * Create a new model.
	 * 
	 * @param system
	 *            The designated outermost function, called "System."
	 */
	public Model model(Function system) {
		return new CommonModel(this, system);
	}

	/**
	 * Create a new scope.
	 * 
	 * @param parent
	 *            The containing scope of this scope. Only null for the
	 *            outermost scope of the designated "System" function.
	 * @param variables
	 *            The set of variables in this scope.
	 * @param function
	 *            The function containing this scope.
	 * @return A new scope
	 */
	public Scope scope(Scope parent, Set<Variable> variables, Function function) {
		Scope newScope = new CommonScope(parent, variables, scopeID++);
		if (parent != null) {
			parent.addChild(newScope);
		}
		newScope.setFunction(function);
		return newScope;
	}

	/**
	 * Get an identifier with the given name.
	 * 
	 * @param name
	 *            The name of this identifier.
	 */
	public Identifier identifier(String name) {
		if (!identifiers.containsKey(name)) {
			identifiers.put(name, new CommonIdentifier(name));
		}
		return identifiers.get(name);
	}

	/**
	 * Create a new variable.
	 * 
	 * @param type
	 *            The type of this variable.
	 * @param name
	 *            The name of this variable.
	 * @param vid
	 *            The index of this variable in its scope.
	 */
	public Variable variable(Type type, Identifier name, int vid) {
		return new CommonVariable(type, name, vid);
	}

	/**
	 * Create a new function.
	 * 
	 * @param name
	 *            The name of this function.
	 * @param parameters
	 *            The list of parameters.
	 * @param returnType
	 *            The return type of this function.
	 * @param containingScope
	 *            The scope containing this function.
	 * @param startLocation
	 *            The first location in the function.
	 * @return The new function.
	 */
	public Function function(Identifier name, Vector<Variable> parameters,
			Type returnType, Scope containingScope, Location startLocation) {
		return new CommonFunction(name, parameters, returnType,
				containingScope, startLocation, this);
	}

	/**
	 * Create a record of a system function.
	 * 
	 * @param name
	 *            The name of this function.
	 */
	public SystemFunction systemFunction(Identifier name) {
		return new CommonSystemFunction(name, new Vector<Variable>(), null,
				null, null, this);
	}

	/**
	 * Create a new location.
	 * 
	 * @param scope
	 *            The scope containing this location.
	 * @return The new location.
	 */
	public Location location(Scope scope) {
		return new CommonLocation(scope, locationID++);
	}

	/* *********************************************************************
	 * Types
	 * *********************************************************************
	 */

	/**
	 * Get the integer primitive type.
	 * 
	 * @return The integer primitive type.
	 */
	public PrimitiveType integerType() {
		return integerType;
	}

	/**
	 * Get the real primitive type.
	 * 
	 * @return The real primitive type.
	 */
	public PrimitiveType realType() {
		return realType;
	}

	/**
	 * Get the boolean primitive type.
	 * 
	 * @return The boolean primitive type.
	 */
	public PrimitiveType booleanType() {
		return booleanType;
	}

	/**
	 * Get the string primitive type.
	 * 
	 * @return The string primitive type.
	 */
	public PrimitiveType stringType() {
		return stringType;
	}

	/**
	 * Get the process type.
	 * 
	 * @return The process type.
	 */
	public ProcessType processType() {
		return processType;
	}

	/**
	 * Get the heap type.
	 * 
	 * @return The heap type.
	 */
	public HeapType heapType() {
		return heapType;
	}

	/**
	 * Get a new array type.
	 * 
	 * @param baseType
	 *            The type of each element in the array.
	 * @return A new array type with the given base type.
	 */
	public ArrayType arrayType(Type baseType) {
		return new CommonArrayType(baseType);
	}

	/**
	 * Get a new pointer type.
	 * 
	 * @param baseType
	 *            The type of element pointed to by the pointer.
	 * @return A new pointer type with the given base type.
	 */
	public PointerType pointerType(Type baseType) {
		return new CommonPointerType(baseType);
	}

	/**
	 * Get a new struct type.
	 * 
	 * @param fields
	 *            List of the fields in this struct type.
	 * @return A new struct type with the given fields.
	 */
	public StructType structType(List<StructField> fields) {
		return new CommonStructType(fields);
	}

	/**
	 * Get a struct field.
	 * 
	 * @param name
	 *            Identifier for the name of this struct member.
	 * @param type
	 *            The type of this struct member.
	 * @return A struct field with the given name and type.
	 */
	public StructField structField(Identifier name, Type type) {
		return new CommonStructField(name, type);
	}

	/* *********************************************************************
	 * Expressions
	 * *********************************************************************
	 */

	/**
	 * A unary expression. One of {-,!}.
	 * 
	 * @param operator
	 *            The unary operator.
	 * @param operand
	 *            The expression to which the operator is applied.
	 * @return The unary expression.
	 */
	public UnaryExpression unaryExpression(UNARY_OPERATOR operator,
			Expression operand) {
		UnaryExpression result = new CommonUnaryExpression(operator, operand);

		result.setExpressionScope(operand.expressionScope());
		return result;
	}

	/**
	 * A binary expression. One of {+,-,*,\,<,<=,==,!=,&&,||,%}
	 * 
	 * @param operator
	 *            The binary operator.
	 * @param left
	 *            The left operand.
	 * @param right
	 *            The right operand.
	 * @return The binary expression.
	 */
	public BinaryExpression binaryExpression(BINARY_OPERATOR operator,
			Expression left, Expression right) {
		BinaryExpression result = new CommonBinaryExpression(operator, left,
				right);

		result.setExpressionScope(join(left.expressionScope(),
				right.expressionScope()));
		return result;
	}

	/**
	 * A cast of an expression to another type.
	 * 
	 * @param type
	 *            The type to which the expression is cast.
	 * @param expresssion
	 *            The expression being cast to a new type.
	 */
	public CastExpression castExpression(Type type, Expression expression) {
		CastExpression result = new CommonCastExpression(type, expression);

		result.setExpressionScope(expression.expressionScope());
		return result;
	}

	/**
	 * The ternary conditional expression ("?" in C).
	 * 
	 * @param condition
	 *            The condition being evaluated in this conditional.
	 * @param trueBranch
	 *            The expression returned if the condition evaluates to true.
	 * @param falseBranch
	 *            The expression returned if the condition evaluates to false.
	 * @return The conditional expression.
	 */
	public ConditionalExpression conditionalExpression(Expression condition,
			Expression trueBranch, Expression falseBranch) {
		ConditionalExpression result = new CommonConditionalExpression(
				condition, trueBranch, falseBranch);

		result.setExpressionScope(join(
				condition.expressionScope(),
				join(trueBranch.expressionScope(),
						falseBranch.expressionScope())));
		return result;
	}

	/**
	 * A boolean literal expression.
	 * 
	 * @param value
	 *            True or false.
	 * @return The boolean literal expression.
	 */
	public BooleanLiteralExpression booleanLiteralExpression(boolean value) {
		if (value) {
			return trueExpression;
		} else {
			return falseExpression;
		}
	}

	/**
	 * An integer literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) integer value.
	 * @return The integer literal expression.
	 */
	public IntegerLiteralExpression integerLiteralExpression(BigInteger value) {
		return new CommonIntegerLiteralExpression(value);
	}

	/**
	 * A real literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) real value.
	 * @return The real literal expression.
	 */
	public RealLiteralExpression realLiteralExpression(BigDecimal value) {
		return new CommonRealLiteralExpression(value);
	}

	/**
	 * This expression is only used in an ensures clause of a function contract
	 * to refer to the returned value.
	 * 
	 * @return A result expression.
	 */
	public ResultExpression resultExpression() {
		return new CommonResultExpression();
	}

	/**
	 * A string literal expression.
	 * 
	 * @param value
	 *            The string.
	 * @return The string literal expression.
	 */
	public StringLiteralExpression stringLiteralExpression(String value) {
		return new CommonStringLiteralExpression(value);
	}

	/**
	 * An expression for an array index operation. e.g. a[i]
	 * 
	 * @param array
	 *            An expression evaluating to an array.
	 * @param index
	 *            An expression evaluating to an integer.
	 * @return The array index expression.
	 */
	public ArrayIndexExpression arrayIndexExpression(Expression array,
			Expression index) {
		ArrayIndexExpression result = new CommonArrayIndexExpression(array,
				index);

		result.setExpressionScope(join(array.expressionScope(),
				index.expressionScope()));
		return result;
	}

	/**
	 * A self expression. Used to referenced the current process.
	 * 
	 * @return A new self expression.
	 */
	public SelfExpression selfExpression() {
		return new CommonSelfExpression();
	}

	/**
	 * A variable expression.
	 * 
	 * @param variable
	 *            The variable being referenced.
	 * @return The variable expression.
	 */
	public VariableExpression variableExpression(Variable variable) {
		VariableExpression result = new CommonVariableExpression(variable);

		// Don't need to worry about the expression scope of constants.
		if (!variable.isConst()) {
			result.setExpressionScope(variable.scope());
		}
		return result;
	}

	/* *********************************************************************
	 * Statements
	 * *********************************************************************
	 */

	/**
	 * An assert statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being asserted.
	 * @return A new assert statement.
	 */
	public AssertStatement assertStatement(Location source,
			Expression expression) {
		AssertStatement result = new CommonAssertStatement(source, expression);

		result.setStatementScope(expression.expressionScope());
		return result;
	}

	/**
	 * An assignment statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param lhs
	 *            The left hand side of the assignment.
	 * @param rhs
	 *            The right hand side of the assignment.
	 * @return A new assignment statement.
	 */
	public AssignStatement assignStatement(Location source, Expression lhs,
			Expression rhs) {
		AssignStatement result = new CommonAssignStatement(source, lhs, rhs);

		result.setStatementScope(join(lhs.expressionScope(),
				rhs.expressionScope()));
		return result;
	}

	/**
	 * An assume statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being added to the path condition.
	 * @return A new assume statement.
	 */
	public AssumeStatement assumeStatement(Location source,
			Expression expression) {
		AssumeStatement result = new CommonAssumeStatement(source, expression);

		result.setStatementScope(expression.expressionScope());
		return result;
	}

	/**
	 * A function call.
	 * 
	 * @param source
	 *            The source location for this call statement.
	 * @param function
	 *            The function.
	 * @param arguments
	 *            The arguments to the function.
	 * @return A new call statement.
	 */
	public CallStatement callStatement(Location source, Function function,
			Vector<Expression> arguments) {
		CallStatement result = new CommonCallStatement(source, function,
				arguments);
		Scope statementScope = null;

		for (Expression arg : arguments) {
			statementScope = join(statementScope, arg.expressionScope());
		}
		result.setStatementScope(statementScope);
		return result;
	}

	/**
	 * A choose statement is of the form x = choose(n);
	 * 
	 * When a choose statement is executed, the left hand side will be assigned
	 * a new symbolic constant. A bound on the values of that symbolic constant
	 * will be added to the path condition.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param lhs
	 *            The left hand side of the choose statement.
	 * @param argument
	 *            The argument to choose().
	 * @return A new choose statement.
	 */
	public ChooseStatement chooseStatement(Location source, Expression lhs,
			Expression argument) {
		ChooseStatement result = new CommonChooseStatement(source, lhs,
				argument, chooseID++);

		result.setStatementScope(join(lhs.expressionScope(),
				argument.expressionScope()));
		return result;
	}

	/**
	 * A fork statement. Used to spawn a new process.
	 * 
	 * @param source
	 *            The source location for this fork statement.
	 * @param function
	 *            An expression evaluating to a function.
	 * @param arguments
	 *            The arguments to the function.
	 * @return A new fork statement.
	 */
	public ForkStatement forkStatement(Location source, Expression function,
			Vector<Expression> arguments) {
		ForkStatement result = new CommonForkStatement(source, null, function,
				arguments);
		Scope statementScope = null;

		for (Expression arg : arguments) {
			statementScope = join(statementScope, arg.expressionScope());
		}
		result.setStatementScope(statementScope);
		return result;
	}

	/**
	 * A fork statement. Used to spawn a new process.
	 * 
	 * @param source
	 *            The source location for this fork statement.
	 * @param lhs
	 *            Expression for place where the process reference will be
	 *            stored. Null if non-existent.
	 * @param function
	 *            An expression evaluating to a function.
	 * @param arguments
	 *            The arguments ot the function.
	 * @return A new fork statement.
	 */
	public ForkStatement forkStatement(Location source, Expression lhs,
			Expression function, Vector<Expression> arguments) {
		ForkStatement result = new CommonForkStatement(source, lhs, function,
				arguments);
		Scope statementScope = lhs.expressionScope();

		for (Expression arg : arguments) {
			statementScope = join(statementScope, arg.expressionScope());
		}
		result.setStatementScope(statementScope);
		return result;
	}

	/**
	 * A join statement. Used to wait for a process to complete.
	 * 
	 * @param source
	 *            The source location for this join statement.
	 * @param process
	 *            An expression evaluating to a process.
	 * @return A new join statement.
	 */
	public JoinStatement joinStatement(Location source, Expression process) {
		JoinStatement result = new CommonJoinStatement(source, process);

		result.setStatementScope(process.expressionScope());
		return result;
	}

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop statement.
	 * @return A new noop statement.
	 */
	public NoopStatement noopStatement(Location source) {
		return new CommonNoopStatement(source);
	}

	/**
	 * A return statement.
	 * 
	 * @param source
	 *            The source location for this return statement.
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 * @return A new return statement.
	 */
	public ReturnStatement returnStatement(Location source,
			Expression expression) {
		ReturnStatement result = new CommonReturnStatement(source, expression);

		if (expression != null) {
			result.setStatementScope(expression.expressionScope());
		}
		return result;
	}

	/**
	 * @param s0
	 *            A scope. May be null.
	 * @param s1
	 *            A scope. May be null.
	 * @return The scope that is the join, or least common ancestor in the scope
	 *         tree, of s0 and s1. Null if both are null. If exactly one of s0
	 *         and s1 are null, returns the non-null scope.
	 */
	private Scope join(Scope s0, Scope s1) {
		Vector<Scope> s0Ancestors = new Vector<Scope>();
		Scope s0Ancestor = s0;
		Scope s1Ancestor = s1;

		if (s0 == null) {
			return s1;
		} else if (s1 == null) {
			return s0;
		}
		s0Ancestors.add(s0Ancestor);
		while (s0Ancestor.parent() != null) {
			s0Ancestor = s0Ancestor.parent();
			s0Ancestors.add(s0Ancestor);
		}
		while (true) {
			if (s0Ancestors.contains(s1Ancestor)) {
				return s1Ancestor;
			}
			s1Ancestor = s1Ancestor.parent();
		}
	}

}
