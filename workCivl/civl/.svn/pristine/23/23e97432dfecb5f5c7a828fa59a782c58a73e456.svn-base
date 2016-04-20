/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.CToken;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BoundVariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression.Quantifier;
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
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
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
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * The factory to create all model components. Usually this is the only way
 * model components will be created.
 * <p>
 * A model consists of a set of functions, including a designated "system"
 * function which is where the execution of the program begins. To create a
 * model, first create the system function using
 * {@link #function(CIVLSource, Identifier, List, CIVLType, Scope, Location)}. A
 * function has a name, parameters, a return type, a containing scope (which is
 * null only in the case of the system function), and a start location. The
 * start location is a location that serves as the beginning of the function's
 * body, and will have one or more outgoing statements.
 * <p>
 * All methods to create statements have a parameter for the location that is
 * the origin location for that statement. Before the new statement is returned,
 * it will be added as an outgoing statement to the specified location. Thus, to
 * add the first statement to a function, call the method to create the new
 * statement and pass the function's start location as a parameter.
 * <p>
 * After constructing the system function, use
 * {@link #model(CIVLSource, CIVLFunction)} to create the model. Additional
 * functions can then be created in the same manner and added to the model with
 * {@link Model#addFunction(CIVLFunction)}.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface ModelFactory {

	/**
	 * @return The symbolic universe
	 */
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
	 * @param source
	 *            The CIVL source of the model
	 * @param system
	 *            The designated outermost function, called "System."
	 * @return A new model
	 */
	Model model(CIVLSource source, CIVLFunction system);

	/**
	 * Create a new scope. This is not used for the outermost scope of a
	 * function, because the outermost scope of a function is created when the
	 * function is constructed.
	 * 
	 * @param source
	 *            The source of the scope
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
	 * @param source
	 *            The CIVL source of the identifier
	 * @param name
	 *            The name of this identifier.
	 * @return The new identifier
	 */
	Identifier identifier(CIVLSource source, String name);

	/**
	 * Create a new variable.
	 * 
	 * @param source
	 *            The CIVL source of the variable
	 * @param type
	 *            The type of this variable.
	 * @param name
	 *            The name of this variable.
	 * @param vid
	 *            The index of this variable in its scope.
	 * @return The variable
	 */
	Variable variable(CIVLSource source, CIVLType type, Identifier name, int vid);

	/**
	 * Create a new function. When the function is constructed, its outermost
	 * scope will be created.
	 * 
	 * @param source
	 *            The CIVL source
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
			List<Variable> parameters, CIVLType returnType,
			Scope containingScope, Location startLocation);

	/**
	 * Generate the system function
	 * 
	 * @param source
	 *            The CIVL source of the function
	 * @param name
	 *            The function name
	 * @param parameters
	 *            The parameters of the function
	 * @param returnType
	 *            The CIVL return type
	 * @param containingScope
	 *            The scope that contains the function
	 * @param libraryName
	 *            The name of the library that defines the function
	 * @return The system function
	 */
	SystemFunction systemFunction(CIVLSource source, Identifier name,
			List<Variable> parameters, CIVLType returnType,
			Scope containingScope, String libraryName);

	/**
	 * Create a new location.
	 * 
	 * @param source
	 *            The CIVL source of the location
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
	 * 
	 * @return The CIVL void type
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
	 * Get the char primitive type.
	 * 
	 * @return The char primitive type.
	 */
	CIVLPrimitiveType charType();

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

	/**
	 * Get the dynamic type.
	 * 
	 * @return The dynamic type.
	 */
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
	 * The struct returned is a new instance of struct type that will never be
	 * equal to another struct type, regardless of identifier or fields.
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

	/**
	 * Create a new bundle type.
	 * 
	 * @return The new bundle type.
	 */
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

	/**
	 * Translate a process id into symbolic expression. When
	 * <code>pid < 0</code>, returns undefinedProcessValue.
	 * 
	 * @param pid
	 *            The process id to be translated
	 * @return The symbolic expression of the process id
	 */
	SymbolicExpression processValue(int pid);

	/**
	 * Translate a symbolic process id into an integer
	 * 
	 * @param source
	 *            The CIVL source information of the symbolic process id
	 * @param processValue
	 *            The symbolic object of the process id
	 * @return The integer of the process id
	 */
	int getProcessId(CIVLSource source, SymbolicExpression processValue);

	/**
	 * Translate an integer scope id into a symbolic expression
	 * 
	 * @param sid
	 *            The scope id to be translated
	 * @return The symbolic expression representing the scope id
	 */
	SymbolicExpression scopeValue(int sid);

	/**
	 * Translate a symbolic scope id into an integer
	 * 
	 * @param source
	 *            The CIVL source information of the symbolic process id
	 * @param scopeValue
	 *            The symbolic object of the scope id
	 * @return The concrete scope id
	 */
	int getScopeId(CIVLSource source, SymbolicExpression scopeValue);

	/* *********************************************************************
	 * Expressions
	 * *********************************************************************
	 */

	/**
	 * A unary expression. One of {-,!}.
	 * 
	 * @param source
	 *            The CIVL source of the expression
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
	 * @param source
	 *            The CIVL source
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
	 * Create a cast expression
	 * 
	 * @param source
	 *            The CIVL source information of the cast expression
	 * @param type
	 *            The type to which the expression is cast.
	 * @param expression
	 *            The expression being cast to a new type.
	 * @return The cast expression created by this method
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
	 * @return The initial value expression
	 */
	InitialValueExpression initialValueExpression(CIVLSource source,
			Variable variable);

	/**
	 * The ternary conditional expression ("?" in C).
	 * 
	 * @param source
	 *            The CIVL source
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
	 * @param source
	 *            The CIVL source
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
	 * @param source
	 *            The CIVL source
	 * @param value
	 *            True or false.
	 * @return The boolean literal expression.
	 */
	BooleanLiteralExpression booleanLiteralExpression(CIVLSource source,
			boolean value);

	/**
	 * An integer literal expression.
	 * 
	 * @param source
	 *            The CIVL source
	 * @param value
	 *            The (arbitrary precision) integer value.
	 * @return The integer literal expression.
	 */
	IntegerLiteralExpression integerLiteralExpression(CIVLSource source,
			BigInteger value);

	/**
	 * A real literal expression.
	 * 
	 * @param source
	 *            The CIVL source
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
	 * @param source
	 *            The CIVL source
	 * @return A result expression.
	 */
	ResultExpression resultExpression(CIVLSource source);

	/**
	 * A string literal expression.
	 * 
	 * @param source
	 *            The CIVL source
	 * @param value
	 *            The string.
	 * @return The string literal expression.
	 */
	StringLiteralExpression stringLiteralExpression(CIVLSource source,
			String value);

	/**
	 * An expression for an array index operation. e.g. a[i]
	 * 
	 * @param source
	 *            The CIVL source
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
	 * @param source
	 *            The CIVL source
	 * @return A new self expression.
	 */
	SelfExpression selfExpression(CIVLSource source);

	/**
	 * A variable expression.
	 * 
	 * @param source
	 *            The CIVL source
	 * @param variable
	 *            The variable being referenced.
	 * @return The variable expression.
	 */
	VariableExpression variableExpression(CIVLSource source, Variable variable);

	/**
	 * Returns a new dereference expression (*p) with operand pointer.
	 * 
	 * @param source
	 *            The CIVL source
	 * @param pointer
	 *            The operand of the dereference operator, an expression with
	 *            pointer type
	 * @return The dereference expression with given operand
	 */
	DereferenceExpression dereferenceExpression(CIVLSource source,
			Expression pointer);

	/**
	 * Returns a new address-of expression <code>(&e)</code> with given operand.
	 * 
	 * @param source
	 *            The CIVL source of the expression
	 * @param operand
	 *            the operand of the address-of operator
	 * @return the address-of expression with given operand
	 */
	AddressOfExpression addressOfExpression(CIVLSource source,
			LHSExpression operand);

	/**
	 * Returns a new quantified expression.
	 * 
	 * @param source
	 *            The source file information for this expression.
	 * @param quantifier
	 *            The quantifier for this quantified expression. One of {FORALL,
	 *            EXISTS, UNIFORM}.
	 * @param boundVariableName
	 *            The name of the bound variable.
	 * @param boundVariableType
	 *            The type of the bound variable.
	 * @param restriction
	 *            The boolean-valued expression involving the bound variable
	 *            which is expected to be true.
	 * @param expression
	 *            The quantified expression.
	 * @return The new quantified expression
	 */
	QuantifiedExpression quantifiedExpression(CIVLSource source,
			Quantifier quantifier, Identifier boundVariableName,
			CIVLType boundVariableType, Expression restriction,
			Expression expression);

	/**
	 * An expression for a bound variable.
	 * 
	 * @param source
	 *            The source file information for this expression.
	 * @param name
	 *            The name of the bound variable being referenced.
	 * @param type
	 *            The type of the bound variable being referenced.
	 * @return The new bound variable expression.
	 */
	BoundVariableExpression boundVariableExpression(CIVLSource source,
			Identifier name, CIVLType type);

	/* *********************************************************************
	 * Statements
	 * *********************************************************************
	 */
	/**
	 * Create a one-statement fragment that contains the assert statement.
	 * 
	 * @param civlSource
	 *            The CIVL source of the assert statement
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being asserted.
	 * @return A new fragment.
	 */
	Fragment assertFragment(CIVLSource civlSource, Location source,
			Expression expression);

	/**
	 * An assignment statement.
	 * 
	 * @param civlSource
	 *            The CIVL source
	 * @param source
	 *            The source location for this statement.
	 * @param lhs
	 *            The left hand side of the assignment.
	 * @param rhs
	 *            The right hand side of the assignment.
	 * @param isInitialization
	 *            True iff the assign statement to create is translated from a
	 *            the initialization node of variable declaration node.
	 * @return A new assignment statement.
	 */
	AssignStatement assignStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, Expression rhs, boolean isInitialization);

	/**
	 * Create a one-statement fragment that contains the assume statement.
	 * 
	 * @param civlSource
	 *            The CIVL source of the assume statement
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being added to the path condition.
	 * @return A new assume statement.
	 */
	Fragment assumeFragment(CIVLSource civlSource, Location source,
			Expression expression);

	/**
	 * A fork statement. Used to spawn a new process.
	 * 
	 * @param civlSource
	 *            The CIVL source of the fork statement
	 * @param source
	 *            The source location for this fork statement.
	 * @param isCall
	 *            is this a call statement (not spawn statement)?
	 * @param function
	 *            A function
	 * @param arguments
	 *            The arguments to the function.
	 * @param guard
	 *            The guard
	 * @return A new fork statement.
	 */
	CallOrSpawnStatement callOrSpawnStatement(CIVLSource civlSource,
			Location source, boolean isCall, CIVLFunction function,
			List<Expression> arguments, Expression guard);

	/**
	 * Create a one-statement fragment that contains the join statement. A join
	 * statement is used to wait for a process to complete.
	 * 
	 * @param civlSource
	 *            The CIVL source of the join statement
	 * @param source
	 *            The source location for this join statement.
	 * @param process
	 *            An expression evaluating to a process.
	 * @return A new fragment.
	 */
	Fragment joinFragment(CIVLSource civlSource, Location source,
			Expression process);

	/**
	 * A noop statement with an explicit guard expression.
	 * 
	 * @param civlSource
	 *            The CIVL source of the no-op statement
	 * @param source
	 *            The source location for this noop statement.
	 * @param guard
	 *            The guard of the noop statement. Must be non-null. For the
	 *            default guard of true, use
	 *            {@link #noopStatement(CIVLSource, Location)}.
	 * @return A new noop statement.
	 */
	NoopStatement noopStatement(CIVLSource civlSource, Location source,
			Expression guard);

	/**
	 * A noop statement with the default guard of true.
	 * 
	 * @param civlSource
	 *            The CIVL source of the no-op statement
	 * @param source
	 *            The source location for this noop statement.
	 * @return A new noop statement with the default guard of true.
	 */
	NoopStatement noopStatement(CIVLSource civlSource, Location source);

	/**
	 * Create a one-statement fragment that contains the return statement.
	 * 
	 * @param civlSource
	 *            The CIVL source of the return statement
	 * @param source
	 *            The source location for this return statement.
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 * @param function
	 *            The CIVL function that this return statement belongs to.
	 * @return A new fragment.
	 */
	Fragment returnFragment(CIVLSource civlSource, Location source,
			Expression expression, CIVLFunction function);

	/**
	 * Create a new malloc statement
	 * 
	 * @param civlSource
	 *            The CIVL source
	 * @param source
	 *            The source location of the malloc statement
	 * @param lhs
	 *            The left hand side of the malloc statement
	 * @param staticElementType
	 *            The static element type
	 * @param heapPointerExpression
	 *            The heap pointer
	 * @param sizeExpression
	 *            The size argument of the malloc statement
	 * @param mallocId
	 *            The id of the malloc statement
	 * @param guard
	 *            The guard
	 * @return The new malloc statement
	 */
	MallocStatement mallocStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, CIVLType staticElementType,
			Expression heapPointerExpression, Expression sizeExpression,
			int mallocId, Expression guard);

	/**
	 * Translate an expression from the CIVL AST to the CIVL model. The
	 * resulting expression will always be boolean-valued. If the expression
	 * evaluates to a numeric type, the result will be the equivalent of
	 * expression==0. Used for evaluating expression in conditions.
	 * 
	 * @param expression
	 *            The expression to be translated.
	 * @return The boolean expression
	 */
	Expression booleanExpression(Expression expression);

	/**
	 * Translate ABC source into CIVL source
	 * 
	 * @param abcSource
	 *            The ABC source
	 * @return The CIVL source
	 */
	CIVLSource sourceOf(Source abcSource);

	/**
	 * Get the CIVL source of a C token
	 * 
	 * @param token
	 *            The C token
	 * @return The CIVL source
	 */
	CIVLSource sourceOfToken(CToken token);

	/**
	 * Get the CIVL source of an AST node
	 * 
	 * @param node
	 *            The AST node
	 * @return The CIVL source
	 */
	CIVLSource sourceOf(ASTNode node);

	/**
	 * Get the CIVL source of the beginning of an AST node
	 * 
	 * @param node
	 *            The AST node
	 * @return The CIVL source
	 */
	CIVLSource sourceOfBeginning(ASTNode node);

	/**
	 * Get the CIVL source of the end of an AST node
	 * 
	 * @param node
	 *            The AST node
	 * @return The CIVL source
	 */
	CIVLSource sourceOfEnd(ASTNode node);

	/**
	 * Translate the span of two ABC sources into CIVL source
	 * 
	 * @param abcSource1
	 *            The first ABC source
	 * @param abcSource2
	 *            The second ABC source
	 * @return The CIVL source
	 */
	CIVLSource sourceOfSpan(Source abcSource1, Source abcSource2);

	/**
	 * Get the CIVL span source of two AST nodes
	 * 
	 * @param node1
	 *            The first AST node
	 * @param node2
	 *            The second AST node
	 * @return The CIVL source
	 */
	CIVLSource sourceOfSpan(ASTNode node1, ASTNode node2);

	/**
	 * Get the span of two CIVL sources
	 * 
	 * @param source1
	 *            The first CIVL source
	 * @param source2
	 *            The second CIVL source
	 * @return The CIVL source
	 */
	CIVLSource sourceOfSpan(CIVLSource source1, CIVLSource source2);

	/**
	 * Check if a certain expression is TRUE.
	 * 
	 * @param expression
	 *            The expression to be checked
	 * @return True iff the expression is TRUE
	 */
	boolean isTrue(Expression expression);

	/**
	 * Set the token factory
	 * 
	 * @param tokens
	 *            The token factory
	 */
	void setTokenFactory(TokenFactory tokens);

	/**
	 * Generate a null pointer expression
	 * 
	 * @param pointerType
	 *            The type of the pointer
	 * @param source
	 *            The CIVL source of the expression
	 * @return The null pointer expression
	 */
	Expression nullPointerExpression(CIVLPointerType pointerType,
			CIVLSource source);

	/**
	 * Translate a conditional expression in to if-else statement. E.g.,
	 * <code>a ? b : c</code> will be translated into
	 * <code>if(a){temp = b;}else{temp = c;}</code> where <code>temp</code> is
	 * the temporal variable.
	 * 
	 * @param guard
	 *            The guard
	 * @param variable
	 *            The temporal variable for the conditional expression
	 * @param expression
	 *            The conditional expression
	 * @return The fragment
	 */
	Fragment conditionalExpressionToIf(Expression guard,
			VariableExpression variable, ConditionalExpression expression);

	/**
	 * Translate a conditional expression in to if-else statement, without
	 * introducing a temporal variable. E.g., <code>x=a ? b : c</code> will be
	 * translated into <code>if(a){x = b;}else{x = c;}</code>. This method is
	 * invoked when only one conditional expression is detected in the
	 * statement.
	 * 
	 * @param expression
	 *            The conditional expression to be translated away.
	 * @param statement
	 *            The statement that has the conditional expression as part of
	 *            it.
	 * @return A new fragment composed by the translated statements
	 */
	Fragment conditionalExpressionToIf(ConditionalExpression expression,
			Statement statement);

	/**
	 * Add a new conditional expression
	 * 
	 * @param expression
	 *            The new conditional expression
	 */
	void addConditionalExpression(ConditionalExpression expression);

	/**
	 * @return True iff the latest queue is not empty
	 */
	boolean hasConditionalExpressions();

	/**
	 * Translate away conditional expressions from a statement. First create a
	 * temporal variable, then replace the conditional expression with the
	 * temporal variable (recursively), then an if-else statement is created to
	 * update the value of the temporal variable, and combine it with the
	 * original statement without condition expressions.
	 * 
	 * @param statement
	 *            The statement that contains conditional expressions
	 * @param oldLocation
	 *            The source location of statement
	 * @return The fragment includes the equivalent if-else statement and the
	 *         modified statement without conditional expressions
	 */
	Fragment refineConditionalExpressionOfStatement(Statement statement,
			Location oldLocation);

	/**
	 * Pop the queue of conditional expressions from the stack. This is invoked
	 * at the end of translating each new statement node, expression node,
	 * variable declaration node, etc.
	 */
	void popConditionaExpressionStack();

	/**
	 * Add a new queue to store conditional expression. This is invoked at the
	 * beginning of translating each new statement node, expression node,
	 * variable declaration node, etc.
	 */
	void addConditionalExpressionQueue();

	/**
	 * Translate a condition that contains conditional expressions in to an
	 * if-else statement
	 * 
	 * @param scope
	 *            The scope of the expression
	 * @param expression
	 *            The expression
	 * @param expressionNode
	 *            The AST node of the expression. Used to construct the start
	 *            and end location of an atomic block when make the resulting
	 *            fragment atomic.
	 * @return The if-else fragment and the expression without conditional
	 *         expressions
	 */
	Pair<Fragment, Expression> refineConditionalExpression(Scope scope,
			Expression expression, ExpressionNode expressionNode);

	/**
	 * @return The earliest conditional expression in the latest queue in the
	 *         stack of conditional expression queues
	 */
	ConditionalExpression pollConditionaExpression();

	// /**
	// * The current translation encounters the starting point of an atomic
	// block
	// */
	// void enterAtomicBlock(boolean deterministic);
	//
	// /**
	// * The current translation reaches the ending point of an atomic block
	// */
	// void leaveAtomicBlock(boolean deterministic);

	// /**
	// *
	// * @return true iff the current translation is inside a certain atomic
	// block
	// */
	// boolean inAtomicBlock();

	/**
	 * A choose statement is of the form <code>x = $choose_int(n)</code>;
	 * 
	 * When a choose statement is executed, the left hand side will be assigned
	 * a new symbolic constant. A bound on the values of that symbolic constant
	 * will be added to the path condition.
	 * 
	 * @param civlSource
	 *            The CIVL source of the choose statement
	 * @param source
	 *            The source location for this statement.
	 * @param lhs
	 *            The left hand side of the choose statement.
	 * @param argument
	 *            The argument to choose_int().
	 * @return A new choose statement.
	 */
	ChooseStatement chooseStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, Expression argument);

	/**
	 * Generate an atomic fragment based on a certain fragment, by adding one
	 * location at before and after the fragment to denote the boundary of the
	 * atomic block
	 * 
	 * @param deterministic
	 *            True iff the atomic block is deterministic (i.e., $atom),
	 *            otherwise it should be a general atomic block (i.e., $atomic).
	 * @param fragment
	 *            The fragment representing the body of the atomic block
	 * @param start
	 *            The start location of the atomic node
	 * @param end
	 *            The end location of the atomic node
	 * @return The new fragment with atomic signs
	 */
	Fragment atomicFragment(boolean deterministic, Fragment fragment,
			Location start, Location end);

	/**
	 * An atomic lock variable is used to keep track of the process that
	 * executes an $atomic block which prevents interleaving with other
	 * processes. This variable is maintained as a global variable
	 * {@link ComonModelFactory#ATOMIC_LOCK_VARIABLE} of <code>$proc</code> type
	 * in the root scope in the CIVL model (always with index 0).
	 * 
	 * @param scope
	 *            The scope of the atomic lock variable, and should always be
	 *            the root scope.
	 */
	void createAtomicLockVariable(Scope scope);

	/**
	 * This method is used in Enabler when a process resumes from being blocked
	 * and wants to get the atomic lock
	 * 
	 * @return The variable expression object of the atomic lock variable
	 */
	VariableExpression atomicLockVariableExpression();

	/**
	 * Create a new statement to assign the atomic lock variable to a specified
	 * process id. The scope of the source location of the resulting statement
	 * 
	 * @param pid
	 *            The id of the process that wants to grab the atomic lock
	 * @param target
	 *            The target location of the resulting statement. The scope of
	 *            the source location will be the same as the target location.
	 * @return The new assign statement that updates the atomic lock variable to
	 *         the specified process id
	 */
	AssignStatement assignAtomicLockVariable(Integer pid, Location target);

	NoopStatement ifBranchStatement(CIVLSource civlSource, Location source,
			Expression guard, boolean isTrue);

	NoopStatement switchBranchStatement(CIVLSource civlSource, Location source,
			Expression guard, Expression label);

	NoopStatement switchBranchStatement(CIVLSource civlSource, Location source,
			Expression guard);

	NoopStatement loopBranchStatement(CIVLSource civlSource, Location source,
			Expression guard, boolean isTrue);

	NoopStatement gotoBranchStatement(CIVLSource civlSource, Location source,
			String label);

	void setImpactScopeOfLocation(Location location);

	void setSystemScope(Scope scope);

}
