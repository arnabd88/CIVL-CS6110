/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.expression.ArrayIndexExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrowExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
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
import edu.udel.cis.vsl.civl.model.IF.type.ProcessType;
import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.civl.model.IF.type.StructType;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * The factory to create all model components. Usually this is the only way
 * model components will be created.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface ModelFactory {

	/**
	 * Create a new model.
	 * 
	 * @param system
	 *            The designated outermost function, called "System."
	 */
	public Model model(Function system);

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
	public Scope scope(Scope parent, Set<Variable> variables, Function function);

	/**
	 * Get an identifier with the given name.
	 * 
	 * @param name
	 *            The name of this identifier.
	 */
	public Identifier identifier(String name);

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
	public Variable variable(Type type, Identifier name, int vid);

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
			Type returnType, Scope containingScope, Location startLocation);

	public SystemFunction systemFunction(Identifier name);

	/**
	 * Create a new location.
	 * 
	 * @param scope
	 *            The scope containing this location.
	 * @return The new location.
	 */
	public Location location(Scope scope);

	/* *********************************************************************
	 * Types
	 * *********************************************************************
	 */

	/**
	 * Get the integer primitive type.
	 * 
	 * @return The integer primitive type.
	 */
	public PrimitiveType integerType();

	/**
	 * Get the real primitive type.
	 * 
	 * @return The real primitive type.
	 */
	public PrimitiveType realType();

	/**
	 * Get the boolean primitive type.
	 * 
	 * @return The boolean primitive type.
	 */
	public PrimitiveType booleanType();

	/**
	 * Get the string primitive type.
	 * 
	 * @return The string primitive type.
	 */
	public PrimitiveType stringType();

	/**
	 * Get the process type.
	 * 
	 * @return The process type.
	 */
	public ProcessType processType();

	/**
	 * Get the heap type.
	 * 
	 * @return The heap type.
	 */
	public HeapType heapType();

	/**
	 * Get a new array type.
	 * 
	 * @param baseType
	 *            The type of each element in the array.
	 * @return A new array type with the given base type.
	 */
	public ArrayType arrayType(Type baseType);

	/**
	 * Get a new pointer type.
	 * 
	 * @param baseType
	 *            The type pointed to by the pointer.
	 * @return A new pointer type with the given base type.
	 */
	public PointerType pointerType(Type baseType);

	/**
	 * Get a new struct type.
	 * 
	 * @param name
	 *            The name of this struct type.
	 * @param fields
	 *            List of the fields in this struct type.
	 * @return A new struct type with the given fields.
	 */
	public StructType structType(Identifier name, List<StructField> fields);

	/**
	 * Get a struct field.
	 * 
	 * @param name
	 *            Identifier for the name of this struct member.
	 * @param type
	 *            The type of this struct member.
	 * @return A struct field with the given name and type.
	 */
	public StructField structField(Identifier name, Type type);

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
			Expression operand);

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
			Expression left, Expression right);

	/**
	 * A cast of an expression to another type.
	 * 
	 * @param type
	 *            The type to which the expression is cast.
	 * @param expresssion
	 *            The expression being cast to a new type.
	 */
	public CastExpression castExpression(Type type, Expression expression);

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
			Expression trueBranch, Expression falseBranch);

	/**
	 * A dot expression is a reference to a struct field.
	 * 
	 * @param struct
	 *            The struct being referenced.
	 * @param field
	 *            The field.
	 * @return The dot expression.
	 */
	public DotExpression dotExpression(Expression struct, Identifier field);

	/**
	 * An arrow expression is a reference to a field in a struct pointer.
	 * 
	 * @param structPointer
	 *            The struct pointer being referenced.
	 * @param field
	 *            The field.
	 * @return The arrow expression.
	 */
	public ArrowExpression arrowExpression(Expression structPointer,
			Identifier field);

	/**
	 * A boolean literal expression.
	 * 
	 * @param value
	 *            True or false.
	 * @return The boolean literal expression.
	 */
	public BooleanLiteralExpression booleanLiteralExpression(boolean value);

	/**
	 * An integer literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) integer value.
	 * @return The integer literal expression.
	 */
	public IntegerLiteralExpression integerLiteralExpression(BigInteger value);

	/**
	 * A real literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) real value.
	 * @return The real literal expression.
	 */
	public RealLiteralExpression realLiteralExpression(BigDecimal value);

	/**
	 * This expression is only used in an ensures clause of a function contract
	 * to refer to the returned value.
	 * 
	 * @return A result expression.
	 */
	public ResultExpression resultExpression();

	/**
	 * A string literal expression.
	 * 
	 * @param value
	 *            The string.
	 * @return The string literal expression.
	 */
	public StringLiteralExpression stringLiteralExpression(String value);

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
			Expression index);

	/**
	 * A self expression. Used to referenced the current process.
	 * 
	 * @return A new self expression.
	 */
	public SelfExpression selfExpression();

	/**
	 * A variable expression.
	 * 
	 * @param variable
	 *            The variable being referenced.
	 * @return The variable expression.
	 */
	public VariableExpression variableExpression(Variable variable);

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
			Expression expression);

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
			Expression rhs);

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
			Expression expression);

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
			Vector<Expression> arguments);

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
			Expression argument);

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
			Vector<Expression> arguments);

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
	 *            The arguments to the function.
	 * @return A new fork statement.
	 */
	public ForkStatement forkStatement(Location source, Expression lhs,
			Expression function, Vector<Expression> arguments);

	/**
	 * A join statement. Used to wait for a process to complete.
	 * 
	 * @param source
	 *            The source location for this join statement.
	 * @param process
	 *            An expression evaluating to a process.
	 * @return A new join statement.
	 */
	public JoinStatement joinStatement(Location source, Expression process);

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop statement.
	 * @return A new noop statement.
	 */
	public NoopStatement noopStatement(Location source);

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
			Expression expression);

}
