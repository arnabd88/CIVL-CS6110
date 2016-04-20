/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collection;
import java.util.Set;
import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ResultExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpressionExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * The factory to create all model components. Usually this is the only way
 * model components will be created.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface ModelFactory {

	SymbolicUniverse universe();

	/**
	 * Returns a source object representing a system-defined object with no link
	 * to actual source code. Used for built-in functions, types, etc.
	 * 
	 * @return a system source object
	 */
	CIVLSource systemSource();

	/**
	 * Create a new model.
	 * 
	 * @param system
	 *            The designated outermost function, called "System."
	 */
	Model model(CIVLSource source, CIVLFunction system);

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
	Scope scope(CIVLSource source, Scope parent, Set<Variable> variables,
			CIVLFunction function);

	/**
	 * Get an identifier with the given name.
	 * 
	 * @param name
	 *            The name of this identifier.
	 */
	Identifier identifier(CIVLSource source, String name);

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
	Variable variable(CIVLSource source, CIVLType type, Identifier name, int vid);

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
	CIVLFunction function(CIVLSource source, Identifier name,
			Vector<Variable> parameters, CIVLType returnType,
			Scope containingScope, Location startLocation);

	SystemFunction systemFunction(CIVLSource source, Identifier name,
			Vector<Variable> parameters, CIVLType returnType,
			Scope containingScope, String libraryName);

	/**
	 * Create a new location.
	 * 
	 * @param scope
	 *            The scope containing this location.
	 * @return The new location.
	 */
	Location location(CIVLSource source, Scope scope);

	/* *********************************************************************
	 * Types
	 * *********************************************************************
	 */

	/**
	 * Returns the void type. Used in places where a type is required
	 * syntactically but there is no type, such as function which does not
	 * return a value.
	 */
	CIVLPrimitiveType voidType();

	/**
	 * Get the integer primitive type.
	 * 
	 * @return The integer primitive type.
	 */
	CIVLPrimitiveType integerType();

	/**
	 * Get the real primitive type.
	 * 
	 * @return The real primitive type.
	 */
	CIVLPrimitiveType realType();

	/**
	 * Get the boolean primitive type.
	 * 
	 * @return The boolean primitive type.
	 */
	CIVLPrimitiveType booleanType();

	/**
	 * Get the string primitive type.
	 * 
	 * @return The string primitive type.
	 */
	CIVLPrimitiveType stringType();

	/**
	 * Get the scope primitive type.
	 * 
	 * @return The scope primitive type.
	 */
	CIVLPrimitiveType scopeType();

	/**
	 * Get the process type.
	 * 
	 * @return The process type.
	 */
	CIVLPrimitiveType processType();

	CIVLPrimitiveType dynamicType();

	/**
	 * Get a new incomplete array type.
	 * 
	 * @param elementType
	 *            The type of each element in the array.
	 * @return A new array type with the given base type.
	 */
	CIVLArrayType incompleteArrayType(CIVLType elementType);

	/**
	 * Returns a new compelte array type with specified extent (length
	 * expression) and element type.
	 * 
	 * @param elementType
	 *            the type of each element in the array
	 * @param extent
	 *            the expression of integer type specifying the length of the
	 *            array
	 * @return the complete array type, as specified
	 */
	CIVLCompleteArrayType completeArrayType(CIVLType elementType,
			Expression extent);

	/**
	 * Get a new pointer type.
	 * 
	 * @param baseType
	 *            The type pointed to by the pointer.
	 * @return A new pointer type with the given base type.
	 */
	CIVLPointerType pointerType(CIVLType baseType);

	/**
	 * Returns new incomplete struct type with given name. Type can be completed
	 * later using one of the "complete" methods in CIVLStructType.
	 * 
	 * @param name
	 *            identifier, usually the "tag" for this struct type
	 * @return a new incomplete struct type with given name
	 */
	CIVLStructType structType(Identifier name);

	/**
	 * Returns a new, incomplete heap type. The heap type must be completed
	 * later by specifying a sequence of malloc statements in method
	 * {@link #completeHeapType}.
	 * 
	 * @param name
	 *            a name to give to the new heap type
	 * 
	 * @return a new incomplete heap type
	 */
	CIVLHeapType heapType(String name);

	/**
	 * Completes the heap type.
	 * 
	 * @param heapType
	 *            an incomplete heap type
	 * @param mallocs
	 *            sequence of malloc statements that can access heaps of that
	 *            type
	 */
	void completeHeapType(CIVLHeapType heapType,
			Collection<MallocStatement> mallocs);

	CIVLBundleType newBundleType();

	/**
	 * Completes the bundle type by specifying the list of all dynamic types
	 * which can occur as bundle elements. If the collections yields a sequence
	 * of types t_i, then the bundlesymbolic type is union_i(array(t_i)).
	 * 
	 * @param bundleType
	 *            an incomplete bundle type
	 * @param types
	 *            the set of all dynamic types which occur as bundle elements
	 */
	void complete(CIVLBundleType bundleType, Collection<SymbolicType> types);

	/**
	 * Returns a new struct field, used to complete a struct type.
	 * 
	 * @param name
	 *            Identifier for the name of this struct member.
	 * @param type
	 *            The type of this struct member.
	 * @return A struct field with the given name and type.
	 */
	StructField structField(Identifier name, CIVLType type);

	/**
	 * Returns the symbolic type used to represent pointers.
	 * 
	 * @return he symbolic type used to represent pointers
	 */
	SymbolicTupleType pointerSymbolicType();

	/**
	 * Returns the symbolic type used to represent process reference values
	 * 
	 * @return the symbolic type used to represent process reference values
	 */
	SymbolicTupleType processSymbolicType();

	/**
	 * Returns the symbolic type used to represent values of type
	 * CIVLDynamicType
	 * 
	 * @return the symbolic type used to represent values of type
	 *         CIVLDynamicType
	 */
	SymbolicTupleType dynamicSymbolicType();

	/**
	 * Returns the symbolic type used to represent scope values
	 * 
	 * @return the symbolic type used to represent scope values
	 */
	SymbolicTupleType scopeSymbolicType();

	/**
	 * Returns the symbolic type used to represent strings
	 * 
	 * @return the symbolic type "array of char"
	 */
	SymbolicArrayType stringSymbolicType();

	SymbolicExpression processValue(int pid);

	int getProcessId(CIVLSource source, SymbolicExpression processValue);

	SymbolicExpression scopeValue(int sid);

	int getScopeId(CIVLSource source, SymbolicExpression scopeValue);

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
	UnaryExpression unaryExpression(CIVLSource source, UNARY_OPERATOR operator,
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
	BinaryExpression binaryExpression(CIVLSource source,
			BINARY_OPERATOR operator, Expression left, Expression right);

	/**
	 * A cast of an expression to another type.
	 * 
	 * @param type
	 *            The type to which the expression is cast.
	 * @param expresssion
	 *            The expression being cast to a new type.
	 */
	CastExpression castExpression(CIVLSource source, CIVLType type,
			Expression expression);

	/**
	 * Returns a new "sizeof(t)" expression.
	 * 
	 * @param source
	 *            source code reference
	 * @param type
	 *            a CIVL type, the argument to "sizeof"
	 * @return the sizeof expression
	 */
	SizeofTypeExpression sizeofTypeExpression(CIVLSource source, CIVLType type);

	/**
	 * Returns a new expression of the form "sizeof(e)" where is an expression.
	 * 
	 * @param source
	 *            source code reference
	 * @param argument
	 *            an expression
	 * @return a new sizeof expression
	 */
	SizeofExpressionExpression sizeofExpressionExpression(CIVLSource source,
			Expression argument);

	/**
	 * Returns a "DynamicTypeOf" expression with the given type argument. This
	 * is an expression of type {@link CIVLDynamicType}. When evaluated in a
	 * state s, it returns an symbolic expression wrapping a symbolic type which
	 * is the type determined by the static type in the given state.
	 * 
	 * @param source
	 *            source code reference
	 * @param type
	 *            static type argument
	 * @return the DynamicTypeOf expression with given argument
	 */
	DynamicTypeOfExpression dynamicTypeOfExpression(CIVLSource source,
			CIVLType type);

	/**
	 * Returns an "initial value" expression for the given variable. This is an
	 * expression which returns the initial value for the variable. It is used
	 * to initialize a variable by assigning it to the variable. The type of
	 * this expression is the type of the variable.
	 * 
	 * @param source
	 * @param variable
	 * @return
	 */
	InitialValueExpression initialValueExpression(CIVLSource source,
			Variable variable);

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
	ConditionalExpression conditionalExpression(CIVLSource source,
			Expression condition, Expression trueBranch, Expression falseBranch);

	/**
	 * A dot expression is a reference to a struct field.
	 * 
	 * @param struct
	 *            The struct being referenced.
	 * @param fieldIndex
	 *            The field index (indexed from 0).
	 * @return The dot expression.
	 */
	DotExpression dotExpression(CIVLSource source, Expression struct,
			int fieldIndex);

	/**
	 * A boolean literal expression.
	 * 
	 * @param value
	 *            True or false.
	 * @return The boolean literal expression.
	 */
	BooleanLiteralExpression booleanLiteralExpression(CIVLSource source,
			boolean value);

	/**
	 * An integer literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) integer value.
	 * @return The integer literal expression.
	 */
	IntegerLiteralExpression integerLiteralExpression(CIVLSource source,
			BigInteger value);

	/**
	 * A real literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) real value.
	 * @return The real literal expression.
	 */
	RealLiteralExpression realLiteralExpression(CIVLSource source,
			BigDecimal value);

	/**
	 * This expression is only used in an ensures clause of a function contract
	 * to refer to the returned value.
	 * 
	 * @return A result expression.
	 */
	ResultExpression resultExpression(CIVLSource source);

	/**
	 * A string literal expression.
	 * 
	 * @param value
	 *            The string.
	 * @return The string literal expression.
	 */
	StringLiteralExpression stringLiteralExpression(CIVLSource source,
			String value);

	/**
	 * An expression for an array index operation. e.g. a[i]
	 * 
	 * @param array
	 *            An expression evaluating to an array.
	 * @param index
	 *            An expression evaluating to an integer.
	 * @return The array index expression.
	 */
	SubscriptExpression subscriptExpression(CIVLSource source,
			LHSExpression array, Expression index);

	/**
	 * A self expression. Used to referenced the current process.
	 * 
	 * @return A new self expression.
	 */
	SelfExpression selfExpression(CIVLSource source);

	/**
	 * A variable expression.
	 * 
	 * @param variable
	 *            The variable being referenced.
	 * @return The variable expression.
	 */
	VariableExpression variableExpression(CIVLSource source, Variable variable);

	/**
	 * Returns a new dereference expression (*p) with operand pointer.
	 * 
	 * @param pointer
	 *            the operand of the dereference operator, an expression with
	 *            pointer type
	 * @return the dereference expression with given operand
	 */
	DereferenceExpression dereferenceExpression(CIVLSource source,
			Expression pointer);

	/**
	 * Returns a new address-of expression (&e) with given operand.
	 * 
	 * @param operand
	 *            the operand of the address-of operator
	 * @return the address-of expression with given operand
	 */
	AddressOfExpression addressOfExpression(CIVLSource source,
			LHSExpression operand);

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
	AssertStatement assertStatement(CIVLSource civlSource, Location source,
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
	AssignStatement assignStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, Expression rhs);

	/**
	 * An assume statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being added to the path condition.
	 * @return A new assume statement.
	 */
	AssumeStatement assumeStatement(CIVLSource civlSource, Location source,
			Expression expression);

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
	ChooseStatement chooseStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, Expression argument);

	/**
	 * A fork statement. Used to spawn a new process.
	 * 
	 * @param source
	 *            The source location for this fork statement.
	 * @param isCall
	 *            is this a call statement (not spawn statement)?
	 * @param function
	 *            A function
	 * @param arguments
	 *            The arguments to the function.
	 * @return A new fork statement.
	 */
	CallOrSpawnStatement callOrSpawnStatement(CIVLSource civlSource,
			Location source, boolean isCall, CIVLFunction function,
			Vector<Expression> arguments);

	/**
	 * A join statement. Used to wait for a process to complete.
	 * 
	 * @param source
	 *            The source location for this join statement.
	 * @param process
	 *            An expression evaluating to a process.
	 * @return A new join statement.
	 */
	WaitStatement joinStatement(CIVLSource civlSource, Location source,
			Expression process);

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop statement.
	 * @return A new noop statement.
	 */
	NoopStatement noopStatement(CIVLSource civlSource, Location source);

	/**
	 * A return statement.
	 * 
	 * @param source
	 *            The source location for this return statement.
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 * @return A new return statement.
	 */
	ReturnStatement returnStatement(CIVLSource civlSource, Location source,
			Expression expression);

	MallocStatement mallocStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, CIVLType staticElementType,
			Expression heapPointerExpression, Expression sizeExpression,
			int mallocId);

}
