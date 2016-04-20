/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.CToken;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.civl.analysis.IF.CodeAnalyzer;
import edu.udel.cis.vsl.civl.model.IF.expression.AbstractFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BoundVariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CharLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ContractClauseExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ContractClauseExpression.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DerivativeCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.HereOrRootExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MemoryUnitExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ProcnullExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression.Quantifier;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RegularRangeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RemoteExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ScopeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.ArraySliceReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.ArraySliceReference.ArraySliceKind;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.SelfReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.StructOrUnionFieldReference;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlParForSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.ModelFactoryException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
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
 * {@link #model(CIVLSource, CIVLFunction, Program)} to create the model.
 * Additional functions can then be created in the same manner and added to the
 * model with {@link Model#addFunction(CIVLFunction)}.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface ModelFactory {

	/* ************************************************************************
	 * CIVL Expressions
	 * ************************************************************************
	 */

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
	 * Create a new instance of array literal expression using an array of
	 * expressions.
	 * 
	 * @param source
	 *            The CIVL source of the array literal.
	 * 
	 * @param arrayType
	 *            The type of the literal.
	 * @param elements
	 *            The elements used to create the array literal expression.
	 * @return The new array literal expression created.
	 */
	ArrayLiteralExpression arrayLiteralExpression(CIVLSource source,
			CIVLArrayType arrayType, List<Expression> elements);

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
	 * Convert an expression to be of boolean-type. The resulting expression
	 * will always be boolean-valued. If the expression evaluates to a numeric
	 * type, the result will be the equivalent of expression!=0. Used for
	 * evaluating expression in conditions.
	 * 
	 * @param expression
	 *            The expression to be translated.
	 * @return The boolean expression
	 * @throws ModelFactoryException
	 *             if the given expression doesn't have boolean type
	 */
	Expression booleanExpression(Expression expression)
			throws ModelFactoryException;

	/**
	 * Translates an expression to be of numeric-type (i.e., int or real).
	 * Basically, if the given expression has boolean type, then it is converted
	 * to a cast expression ((int)expression). Otherwise, if it is not of
	 * numeric type, an exception will be thrown.
	 * 
	 * @param expression
	 * @return the numeric representation of the given expression
	 * @throws ModelFactoryException
	 *             if the given expression doesn't have boolean or numeric type
	 */
	Expression numericExpression(Expression expression)
			throws ModelFactoryException;

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

	/**
	 * Creates a character literal expression with the given character value.
	 * 
	 * @param sourceOf
	 *            The source of the new expression
	 * @param value
	 *            The character value of the expression
	 * @return a new character literal expression with the given character
	 *         value.
	 */
	CharLiteralExpression charLiteralExpression(CIVLSource sourceOf, char value);

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
	 * Returns a "DynamicTypeOf" expression with the given type argument. When
	 * evaluated in a state s, it returns an symbolic expression wrapping a
	 * symbolic type which is the type determined by the static type in the
	 * given state.
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
	 * creates a function identifier expression.
	 * 
	 * @param source
	 * @param function
	 * @return the new function identifier expression of the given function
	 */
	FunctionIdentifierExpression functionIdentifierExpression(
			CIVLSource source, CIVLFunction function);

	/**
	 * @param source
	 * @param isRoot
	 *            true if the expression to be created is <code>$root</code>;
	 *            otherwise, <code>$here</code>
	 * @return a new here or root expression
	 */
	HereOrRootExpression hereOrRootExpression(CIVLSource source, boolean isRoot);

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
	 * Creates a <code>$proc_null</code> constant expression.
	 * 
	 * @param source
	 *            The source of the <code>$proc_null</code>
	 * @return the new <code>$proc_null</code> constant expression
	 */
	ProcnullExpression procnullExpression(CIVLSource source);

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
	 * @param lower
	 *            The integer-valued expression for the lower end of the bound
	 *            variable range.
	 * @param upper
	 *            The integer-valued expression for the upper end of the bound
	 *            variable range.
	 * @param expression
	 *            The quantified expression.
	 * @return The new quantified expression
	 */
	QuantifiedExpression quantifiedExpression(CIVLSource source,
			Quantifier quantifier, Identifier boundVariableName,
			CIVLType boundVariableType, Expression lower, Expression upper,
			Expression expression);

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
	 * Creates a regular range expression, which has the syntax
	 * <code>low .. high # step</code>. step should be non-zero, and
	 * <code>(high-low)/step >= 0 </code>.
	 * 
	 * @param source
	 *            the source code information of the regular range expression.
	 * @param low
	 *            the lower bound of the range
	 * @param high
	 *            the higher bound of the range
	 * @param step
	 *            the step of the range
	 * @return the new regular range expression with the given lower/upper
	 *         bounds and step.
	 */
	RegularRangeExpression regularRangeExpression(CIVLSource source,
			Expression low, Expression high, Expression step);

	/**
	 * Create a rectangular domain expression, which has the form
	 * <code>{r1, r2, ..., rm}</code>, where <code>m</code> is the dimension of
	 * the domain, and <code>ri (where 1 <= i <= m)</code> is a range expression
	 * (either regular range or literal range).
	 * 
	 * @param source
	 *            the source code information of the domain expression
	 * @param ranges
	 *            the list of range expressions that will be used to compose the
	 *            domain expression
	 * @param type
	 *            the type of the domain expression
	 * @return the new rectangular domain expression.
	 */
	RecDomainLiteralExpression recDomainLiteralExpression(CIVLSource source,
			List<Expression> ranges, CIVLType type);

	/**
	 * Returns a domain guard expression which is boolean expression whose
	 * arguments consists of loop variables in a CIVL <code>$for</code> loop and
	 * the original domain associate to the loop. It evaluates it to true if and
	 * only if the values of those variables are such that at least one more
	 * iteration exists.
	 * 
	 * @param source
	 *            the source code information of the domain guard expression
	 * @param vars
	 *            the list of variables the value of which represent the current
	 *            element of the domain
	 * @param counter
	 *            the counter variable for iterating the domain one by one
	 * @param domain
	 *            the domain
	 * @return the new domain guard expression.
	 */
	DomainGuardExpression domainGuard(CIVLSource source, List<Variable> vars,
			Variable counter, Expression domain);

	/**
	 * Creates a new $scopeof expression using the given argument.
	 * 
	 * @param source
	 *            The source code element to be used for error report.
	 * @param argument
	 *            The argument of the scope of expression.
	 * @return The new $scopeof expression.
	 */
	ScopeofExpression scopeofExpression(CIVLSource source,
			LHSExpression argument);

	/**
	 * A self expression. Used to referenced the current process.
	 * 
	 * @param source
	 *            The CIVL source
	 * @return A new self expression.
	 */
	SelfExpression selfExpression(CIVLSource source);

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
	SizeofExpression sizeofExpressionExpression(CIVLSource source,
			Expression argument);

	/**
	 * Creates a new instance of struct or union literal expression
	 * 
	 * @param source
	 *            the source of the literal expression
	 * @param type
	 *            the type of the literal expression
	 * @param fields
	 *            the fields of the struct/union expression
	 * @return the new struct or union literal expression
	 */
	StructOrUnionLiteralExpression structOrUnionLiteralExpression(
			CIVLSource source, CIVLType type, List<Expression> fields);

	/**
	 * Creates a new instance of struct or union literal expression, which has a
	 * constant value.
	 * 
	 * @param source
	 *            the source of the literal expression
	 * @param exprScope
	 *            the scope of the literal expression
	 * @param type
	 *            the type of the literal expression
	 * @param constantValue
	 *            the constant value of the literal
	 * @return the new struct or union literal expression which has the given
	 *         constant value
	 */
	StructOrUnionLiteralExpression structOrUnionLiteralExpression(
			CIVLSource source, Scope exprScope, CIVLType type,
			SymbolicExpression constantValue);

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
	 * creates a system function call expression
	 * 
	 * @param callStatement
	 * @return the new expression which contains a call to a system function.
	 */
	SystemFunctionCallExpression systemFunctionCallExpression(
			CallOrSpawnStatement callStatement);

	/**
	 * creates a new boolean expression which has the value $true
	 * 
	 * @param source
	 *            the source of the expression
	 * @return the new boolean expression which has the value $true
	 */
	Expression trueExpression(CIVLSource source);

	/**
	 * Creates the system guard expression for the given system call statement.
	 * <p>
	 * Precondition:
	 * <code>sysCall.isCall == true && sysCall.isSystemCall() == true</code>.
	 * 
	 * @param sysCall
	 *            The system call statement.
	 * @return the expression that represents the guard of a system function
	 *         call
	 */
	Expression systemGuardExpression(CallOrSpawnStatement sysCall);

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
	 * An expression for a call to an abstract function.
	 * 
	 * @param source
	 *            The source file information for this expression.
	 * @param function
	 *            The abstract function being called.
	 * @param arguments
	 *            The arguments to the function call.
	 * @return The new abstract function call expression.
	 */
	AbstractFunctionCallExpression abstractFunctionCallExpression(
			CIVLSource source, AbstractFunction function,
			List<Expression> arguments);

	/**
	 * An expression for a call to the derivative of an abstract function.
	 * 
	 * @param source
	 *            The source file information for this expression.
	 * @param function
	 *            The abstract function being called.
	 * @param partials
	 *            The pairs representing which partial derivatives are taken.
	 *            Each pair is comprised of the variable for the parameter in
	 *            which the partial derivative is taken, and an integer
	 *            indicating how many times that partial is taken.
	 * @param arguments
	 *            The arguments to the function call.
	 * @return The new derivative call expression.
	 */
	DerivativeCallExpression derivativeCallExpression(CIVLSource source,
			AbstractFunction function,
			List<Pair<Variable, IntegerLiteralExpression>> partials,
			List<Expression> arguments);

	/* ************************************************************************
	 * Memory Unit Expressions
	 * ************************************************************************
	 */

	/**
	 * creates a new array slice reference.
	 * 
	 * @param sliceKind
	 *            the kind of the array slice
	 * @param index
	 *            the index expression for the slice, which could be of integer
	 *            or domain type
	 * @return the new array slice reference
	 */
	ArraySliceReference arraySliceReference(ArraySliceKind sliceKind,
			Expression index);

	/**
	 * @return a self reference
	 */
	SelfReference selfReference();

	/**
	 * creates a reference to a certain field of a struct
	 * 
	 * @param fieldIndex
	 *            the index of the field referred to
	 * @return the new reference to the field at the specified index of a struct
	 */
	StructOrUnionFieldReference structFieldReference(int fieldIndex);

	/**
	 * creates a memory unit expression.
	 * 
	 * @param source
	 *            the source of the expression
	 * @param variable
	 *            the variable that the memory unit corresponds to
	 * @param objetType
	 *            the type of the object that the memory unit references
	 * @param reference
	 *            the reference corresponds to the variable
	 * @param writable
	 *            the access status of the memory unit
	 * @param hasPinterRef
	 *            does the memory unit contains any pointer reference?
	 * @return the new memory unit expression
	 */
	MemoryUnitExpression memoryUnitExpression(CIVLSource source,
			Variable variable, CIVLType objetType,
			MemoryUnitReference reference, boolean writable,
			boolean hasPinterRef);

	/* ************************************************************************
	 * Fragments and Statements
	 * ************************************************************************
	 */

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
	 * Creates a call or spawn statement. In the case of call, it could be a
	 * normal function call, or a system function call.
	 * 
	 * @param sourceOf
	 *            The CIVL source of the call or spawn statement
	 * @param location
	 *            The source location for the call or spawn statement.
	 * @param isCall
	 *            is this a call statement (not spawn statement)?
	 * @param function
	 *            The function identifier expression, null if the function is
	 *            not a variable.
	 * @param arguments
	 *            The arguments to the function.
	 * @param guard
	 *            The guard of the statement
	 * @return the new call or spawn statement
	 */
	CallOrSpawnStatement callOrSpawnStatement(CIVLSource sourceOf,
			Location location, boolean isCall, Expression function,
			List<Expression> arguments, Expression guard);

	/**
	 * creates a <code>$parfor</code> enter statement to start the execution of
	 * the <code>$parfor</code>.
	 * 
	 * @param source
	 *            the source of the <code>$parfor</code> enter statement
	 * @param location
	 *            the source location of the <code>$parfor</code> enter
	 *            statement
	 * @param domain
	 *            the domain of the <code>$parfor</code> statement
	 * @param domSize
	 * 
	 * @param procsVar
	 *            the variable expression representing the array for the
	 *            references of processes that are to be spawned by the $parfor
	 * @param parProcFunc
	 *            the function that represents the body of the
	 *            <code>$parfor</code>
	 * @return the new <code>$parfor</code> enter statement
	 */
	CivlParForSpawnStatement civlParForEnterStatement(CIVLSource source,
			Location location, Expression domain, VariableExpression domSize,
			VariableExpression procsVar, CIVLFunction parProcFunc);

	/**
	 * A goto branch statement is of the form <code> goto label; </code>. When a
	 * goto branch statement is executed, no variables will be updated but only
	 * the location of the process will be updated to the target of the goto
	 * branch statement.
	 * 
	 * @param civlSource
	 *            The source of this goto statement.
	 * @param source
	 *            The source location of this goto statement.
	 * @param label
	 *            The label of the target of the goto statement.
	 * @return A new goto branch statement.
	 */
	NoopStatement gotoBranchStatement(CIVLSource civlSource, Location source,
			String label);

	/**
	 * An if-else branch statement is introduced to translate if-else statement.
	 * It could be either the if-branch statement or the else-branch statement.
	 * 
	 * @param civlSource
	 *            The source of this if-else branch statement.
	 * @param source
	 *            The source location of this if branch statement.
	 * @param guard
	 *            The guard of the if-else branch statement. Given an statement
	 *            like <code>if(c)a;else b; </code>, the guard of the if branch
	 *            is <code>a</code>, whereas the guard for the else branch is
	 *            <code>!a</code>.
	 * @param isIf
	 *            True iff the branch is the if branch, otherwise, it is the
	 *            else branch.
	 * @return
	 */
	NoopStatement ifElseBranchStatement(CIVLSource civlSource, Location source,
			Expression guard, boolean isIf);

	/**
	 * An loop branch statement is introduced when translating a loop. It could
	 * be the branch for the loop condition being either true or false.
	 * 
	 * @param civlSource
	 *            The CIVL source of the loop branch statement.
	 * @param source
	 *            The source location of the loop branch statement.
	 * @param guard
	 *            The guard of the loop branch statement. Given an statement
	 *            like <code>while(a)b; </code>, the guard of the loop-true
	 *            branch is <code>a</code>, whereas the guard for the loop-false
	 *            branch is <code>!a</code>.
	 * @param isTrue
	 *            True if the statement is for the loop-true branch, otherwise
	 *            for the loop-false branch.
	 * @return
	 */
	NoopStatement loopBranchStatement(CIVLSource civlSource, Location source,
			Expression guard, boolean isTrue);

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
	 * A noop statement with the default guard of true.
	 * 
	 * @param civlSource
	 *            The CIVL source of the no-op statement
	 * @param source
	 *            The source location for this noop statement.
	 * @param expression
	 *            The expression associates with this noop statement.
	 * @return A new noop statement with the default guard of true.
	 */
	NoopStatement noopStatement(CIVLSource civlSource, Location source,
			Expression expression);

	/**
	 * A temporary noop statement with the true guard
	 * 
	 * @param civlSource
	 *            The CIVL source of the no-op statement
	 * @param source
	 *            The source location for this noop statement.
	 * @return A new temporary noop statement with the true guard
	 */
	NoopStatement noopStatementTemporary(CIVLSource civlSource, Location source);

	/**
	 * A temporary noop statement with the true guard
	 * 
	 * @param civlSource
	 *            The CIVL source of the no-op statement
	 * @param source
	 *            The source location for this noop statement.
	 * @return A new temporary noop statement with the true guard
	 */
	NoopStatement noopStatementForVariableDeclaration(CIVLSource civlSource,
			Location source);

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
	NoopStatement noopStatementWtGuard(CIVLSource civlSource, Location source,
			Expression guard);

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
	 * Creates a switch branch statement for the default case, which is a
	 * subclass of no-op statement.
	 * 
	 * @param civlSource
	 *            The CIVL source of the default case
	 * @param source
	 *            The source location for this statement
	 * @param guard
	 *            The guard of the branch statement
	 * @return the new switch branch statement for the default case
	 */
	NoopStatement switchBranchStatement(CIVLSource civlSource, Location source,
			Expression guard);

	/**
	 * Creates a switch branch statement for a labeled case.
	 * 
	 * @param civlSource
	 *            The CIVL source of the default case
	 * @param source
	 *            The source location for this statement
	 * @param guard
	 *            The guard of the branch statement
	 * @param label
	 *            The label of the case
	 * @return the new switch branch statement for the specified case
	 */
	NoopStatement switchBranchStatement(CIVLSource civlSource, Location source,
			Expression guard, Expression label);

	/* *********************************************************************
	 * CIVL Source
	 * *********************************************************************
	 */

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
	 * Returns a source object representing a system-defined object with no link
	 * to actual source code. Used for built-in functions, types, etc.
	 * 
	 * @return a system source object
	 */
	CIVLSource systemSource();

	/* *********************************************************************
	 * Translating away conditional expressions
	 * *********************************************************************
	 */

	/**
	 * Add a new conditional expression
	 * 
	 * @param expression
	 *            The new conditional expression
	 */
	void addConditionalExpression(ConditionalExpression expression);

	/**
	 * Add a new queue to store conditional expression. This is invoked at the
	 * beginning of translating each new statement node, expression node,
	 * variable declaration node, etc.
	 */
	void addConditionalExpressionQueue();

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
	 * @return True iff the latest queue is not empty
	 */
	boolean hasConditionalExpressions();

	/**
	 * Pop the queue of conditional expressions from the stack. This is invoked
	 * at the end of translating each new statement node, expression node,
	 * variable declaration node, etc.
	 */
	void popConditionaExpressionStack();

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
			Expression expression, CIVLSource startSource, CIVLSource endSource);

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

	/* *********************************************************************
	 * Atomic Lock Variable
	 * *********************************************************************
	 */

	/**
	 * This method is used in Enabler when a process resumes from being blocked
	 * and wants to get the atomic lock
	 * 
	 * @return The variable expression object of the atomic lock variable
	 */
	VariableExpression atomicLockVariableExpression();

	/* *********************************************************************
	 * Identifier, Function, Location, Model, Scope, Variable
	 * *********************************************************************
	 */

	/**
	 * Generate an abstract function.
	 * 
	 * @param source
	 *            The CIVL source of the function.
	 * @param name
	 *            The function name.
	 * @param parameters
	 *            The parameters of the function.
	 * @param returnType
	 *            The CIVL return type
	 * @param containingScope
	 *            The scope that contains the function.
	 * @param continuity
	 *            The total number of partial derivatives of this function that
	 *            may be taken.
	 * @return The abstract function.
	 */
	AbstractFunction abstractFunction(CIVLSource source, Identifier name,
			List<Variable> parameters, CIVLType returnType,
			Scope containingScope, int continuity);

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
	 * Create a new location.
	 * 
	 * @param source
	 *            The CIVL source of the location
	 * @param scope
	 *            The scope containing this location.
	 * @return The new location.
	 */
	Location location(CIVLSource source, Scope scope);

	/**
	 * Create a new model.
	 * 
	 * @param source
	 *            The CIVL source of the model
	 * @param system
	 *            The designated outermost function, called "System."
	 * @return A new model
	 */
	Model model(CIVLSource source, CIVLFunction system, Program program);

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

	/* *********************************************************************
	 * Setters and Getters
	 * *********************************************************************
	 */

	/**
	 * Returns the CIVL model built by this model factory.
	 * 
	 * @return the CIVL model built by this model factory.
	 */
	Model model();

	Variable timeCountVariable();

	Variable brokenTimeVariable();

	/**
	 * Set the token factory
	 * 
	 * @param tokens
	 *            The token factory
	 */
	void setTokenFactory(TokenFactory tokens);

	/**
	 * Set the system scope, which is the root (static) scope of the model.
	 * 
	 * @param scope
	 *            The system scope of the model
	 */
	void setSystemScope(Scope scope);

	/**
	 * Gets the CIVL type factory associates with this model factory.
	 * 
	 * @return the CIVL type factory
	 */
	CIVLTypeFactory typeFactory();

	/**
	 * @return The symbolic universe
	 */
	SymbolicUniverse universe();

	/* ************************************************************************
	 * Symbolic Expressions: Dyscope References
	 * ************************************************************************
	 */

	/**
	 * Translate a symbolic scope id into an integer. A symbolic scope id is a
	 * tuple with one element of integer type. A CIVL internal exception is
	 * thrown if the value can't be computed.
	 * 
	 * @param source
	 *            The CIVL source information of the symbolic process id
	 * @param scopeValue
	 *            The symbolic object of the scope id
	 * @return The concrete scope id
	 */
	int getScopeId(CIVLSource source, SymbolicExpression scopeValue);

	boolean isScopeIdDefined(int scopeId);

	/**
	 * Translate an integer scope id into a symbolic expression
	 * 
	 * @param sid
	 *            The scope id to be translated
	 * @return The symbolic expression representing the scope id
	 */
	SymbolicExpression scopeValue(int sid);

	/* ************************************************************************
	 * Symbolic Expressions: Process References
	 * ************************************************************************
	 */

	/**
	 * Translate a symbolic process id into an integer. A symbolic process id is
	 * a tuple with one element of integer type.
	 * 
	 * @param source
	 *            The CIVL source information of the symbolic process id
	 * @param processValue
	 *            The symbolic object of the process id
	 * @return The integer of the process id
	 */
	int getProcessId(CIVLSource source, SymbolicExpression processValue);

	/**
	 * Checks if the given process value equals to the $proc_null constant. An
	 * error is reported if the given process value is not of $proc type.
	 * 
	 * @param source
	 *            The source code element for error report.
	 * @param procValue
	 *            The process value to be checked.
	 * @return True iff the given process value equals to the $proc_null
	 *         constant.
	 */
	boolean isProcNull(CIVLSource source, SymbolicExpression procValue);

	SymbolicExpression nullProcessValue();

	boolean isPocessIdDefined(int pid);

	boolean isProcessIdNull(int pid);

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
	 * generate undefined value of a certain type
	 * 
	 * @param type
	 * @return
	 */
	SymbolicExpression undefinedValue(SymbolicType type);

	/* ************************************************************************
	 * Malicious
	 * ************************************************************************
	 */

	/**
	 * Check if a certain expression is TRUE.
	 * 
	 * @param expression
	 *            The expression to be checked
	 * @return True iff the expression is TRUE
	 */
	boolean isTrue(Expression expression);

	/**
	 * Computes the impact scope of a location, which is the highest scope that
	 * the location accesses. This method has side effect on the location.
	 * 
	 * @param location
	 *            The location whose impact scope is to be computed.
	 */
	void computeImpactScopeOfLocation(Location location);

	/**
	 * Creates an anonymous variable of array type in a certain scope. An
	 * anonymous variable has the name "_anon_i", like "_anon_0", "_anon_1",
	 * etc.
	 * 
	 * @param sourceOf
	 *            The source of the variable
	 * @param scope
	 *            The scope of the new anonymous variable
	 * @param type
	 *            The type of the new anonymous variable
	 * @return the new anonymous variable
	 */
	Variable newAnonymousVariableForArrayLiteral(CIVLSource sourceOf,
			CIVLArrayType type);

	/**
	 * Returns the current fragment of an assignment statement for an anonymous
	 * variable initialization. When translating a string literal or an array
	 * literal of characters, if it is used as the initializer of a variable of
	 * pointer type, then an anonymous (constant) variable of array of character
	 * is created in the top scope (i.e., system scope).
	 * 
	 * @return
	 */
	Fragment anonFragment();

	/**
	 * Clear the current anonymous fragment. See {@link #anonFragment()} for
	 * more about anonymous fragments.
	 */
	void clearAnonFragment();

	/**
	 * Add the given statement to the anonymous fragment.
	 * 
	 * @param statment
	 *            The statement to be added to the anonymous fragment.
	 */
	void addAnonStatement(Statement statment);

	Expression functionGuardExpression(CIVLSource source, Expression function,
			List<Expression> arguments);

	VariableExpression civlFilesystemVariableExpression();

	/**
	 * Returns a new fragment containing a CivlForStatement.
	 * 
	 * @param source
	 * @param src
	 * @param dom
	 * @param variables
	 * @return
	 */
	Fragment civlForEnterFragment(CIVLSource source, Location src,
			Expression dom, List<Variable> variables, Variable counter);

	VariableExpression domSizeVariable(CIVLSource source, Scope scope);

	VariableExpression parProcsVariable(CIVLSource source, CIVLType type,
			Scope scope);

	FunctionIdentifierExpression waitallFunctionPointer();

	FunctionIdentifierExpression elaborateDomainPointer();

	/**
	 * Get the name of the counter variable for the for loop on a literal domain
	 * 
	 * @return the identifier wrapping the name of the variable
	 */
	Identifier getLiteralDomCounterIdentifier(CIVLSource source, int count);

	/**
	 * Create a variable of the given type and add it to the given scope.
	 * 
	 * @param sourceOf
	 * @param scope
	 * @param type
	 * @return
	 */
	Variable newAnonymousVariable(CIVLSource sourceOf, Scope scope,
			CIVLType type);

	/**
	 * The list of code analyzers associate with this model.
	 * 
	 * @return
	 */
	List<CodeAnalyzer> codeAnalyzers();

	void setCodeAnalyzers(List<CodeAnalyzer> analyzers);

	List<Variable> inputVariables();

	void addInputVariable(Variable variable);

	/**
	 * Creates a remote reference expression with a numeric expression
	 * represents a process and a variable identifier expression.
	 * 
	 * @param source
	 * @param process
	 * @param scope
	 * @return
	 */
	RemoteExpression remoteExpression(CIVLSource source, Expression expression,
			Expression process, Scope scope);

	/**
	 * Creates a contract clause expression: {@link ContractClauseExpression}.
	 * 
	 * @param source
	 *            CIVLSource of the contract clause
	 * @param type
	 *            Expression type, should can only be Boolean Type
	 * @param collectiveGroup
	 *            Expression of the group of processes, only significant when
	 *            this contract is a collective contract.
	 * @param body
	 *            Expression of the body of this contract clause which should be
	 *            a boolean expression.
	 * @param contractKind
	 *            The kind of the contract, e.g. Requires or Ensures
	 * @param contractCalls
	 *            System function calls supported by contract semantics, can be
	 *            null if there is no such call.
	 * @return
	 */
	ContractClauseExpression contractClauseExpression(CIVLSource source,
			CIVLType type, Expression collectiveGroup, Expression body,
			ContractKind contractKind);
}
