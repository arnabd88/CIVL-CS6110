/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.IF.expr;

import edu.udel.cis.vsl.sarl.IF.object.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.object.CharObject;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * <p>
 * An instance {@link SymbolicExpression} represents a symbolic expression. This
 * is the root of the symbolic expression type hierarchy.
 * </p>
 * 
 * <p>
 * A {@link SymbolicExpression} is a kind of {@link SymbolicObject}. Like all
 * symbolic objects, symbolic expressions are immutable: they cannot be modified
 * after they are instantiated. (Or at least, not in a way visible to the user.)
 * </p>
 * 
 * <p>
 * A symbolic expression has an operator (instance of {@link SymbolicOperator}),
 * a type ({@link SymbolicType}), and some number of arguments, which together
 * fully specify the expression. The arguments implement the
 * {@link SymbolicObject} interface. {@link SymbolicExpression} extends
 * {@link SymbolicObject}, so a symbolic expression can be used as an argument
 * (but so can other kinds of symbolic objects).
 * </p>
 * 
 * <p>
 * The difference between symbolic expressions and symbolic objects which are
 * not symbolic expressions is that the latter may have essential fields that
 * are not arguments. (An essential field is used in the "equals" method.) In
 * contrast, a symbolic expression is completely determined by its operator,
 * type, and arguments.
 * </p>
 * 
 * <p>
 * TO POSSIBLY DO: add IFF (if and only if), add IMPLIES, let quantifiers take
 * multiple variables.
 * </p>
 * 
 * @author siegel
 */
public interface SymbolicExpression extends SymbolicObject {

	/**
	 * An enumerated type for the different kinds of symbolic expressions.
	 */
	public enum SymbolicOperator {
		/**
		 * Operator for an expression representing the sum of its arguments. The
		 * arguments and the expression are all instances of
		 * {@link NumericExpression}. The arguments must all have the same
		 * numeric (integer or real) type, which is also the type of the
		 * expression. There can be any number of arguments (including 0). The
		 * sum with 0 arguments is equivalent to the 0 of the type of the
		 * expression.
		 */
		ADD,
		/**
		 * Operator for an expression representing the conjunction of symbolic
		 * expressions of boolean type. The arguments and the expression are all
		 * instances of {@link BooleanExpression}. The arguments and the
		 * expression itself all have boolean type. There can be any number of
		 * arguments (including 0). The conjunction with 0 arguments is
		 * equivalent to the "true" expression.
		 * 
		 * @see #OR
		 * @see #NOT
		 */
		AND,
		/**
		 * Operator for an expression representing the application of a function
		 * to some arguments. Takes 2 arguments. Arg0 is a
		 * {@link SymbolicExpression} of {@link SymbolicFunctionType}. Arg1 is
		 * an
		 * <code>{@link Iterable}&lt;? extends {@link SymbolicExpression}&gt;</code>
		 * containing the ordered sequence of arguments to the function.
		 */
		APPLY,
		/**
		 * A concrete array. The arguments are the elements of the array.
		 */
		ARRAY,
		/**
		 * Operator for an array expression of type <i>T</i>[] formed by
		 * providing a function <i>f</i> from integers to <i>T</i>. Has one
		 * argument: a symbolic expression <i>f</i> of
		 * {@link SymbolicFunctionType}. Note that the length of the array may
		 * (or may not) be specified in the type of the resulting expression.
		 */
		ARRAY_LAMBDA,
		/**
		 * Operator for an expression representing the result of reading an
		 * element from an array. 2 arguments. Arg0 is the array expression (a
		 * symbolic expression of {@link SymbolicArrayType}), Arg1 is the index
		 * expression (a {@link SymbolicExpression} of integer type).
		 * 
		 * @see ARRAY_WRITE
		 */
		ARRAY_READ,
		/**
		 * Operator for an expression representing the array resulting from
		 * modifying a single element of an array. 3 Arguments. Arg0 is the
		 * original array expression, arg1 is the index expression, arg2 is the
		 * new value being assigned to that position in the array.
		 * 
		 * @see #ARRAY_READ
		 */
		ARRAY_WRITE,
		/**
		 * Operator for an expression representing the result of converting a
		 * value from one type to another. 1 argument: the value being cast. The
		 * {@link #type()} method in this expression yields the new type to
		 * which the element is being cast.
		 */
		CAST,
		/**
		 * TODO: this will go away in the refactoring.
		 * 
		 * Operator for a concrete value acting as a symbolic expression. One
		 * argument, which is the concrete value. Argument may be
		 * {@link BooleanObject}, {@link NumberObject}, {@link CharObject}, or
		 * an
		 * <code>{@link Iterable}&lt;? extends {@link SymbolicExpression}&gt;</code>
		 * . The last case is used to represent concrete values for arrays or
		 * tuples.
		 */
		CONCRETE,
		/**
		 * Operator for a conditional expression, also known as "if-then-else",
		 * as in C's ternary expression <code>arg0 ? arg1 : arg2</code>. 3
		 * arguments. Arg0 is the boolean predicate expression (an instance of
		 * {@link BooleanExpression}), arg1 is the expression which is the
		 * result if arg0 evaluates to <code>true</code>, arg2 the expression
		 * which is the result if arg0 evaluates to <code>false</code>. arg1 and
		 * arg2 must have the same type, which is the type of the conditional
		 * expression.
		 */
		COND,
		/**
		 * Operator for expression that represents the result of multiple writes
		 * to distinct concrete positions in an array. 2 arguments. Arg0 is an
		 * expression of {@link SymbolicArrayType} <i>T[]</i>. Arg1 is an
		 * <code>{@link Iterable}&lt;? extends {@link SymbolicExpression}&gt;</code>
		 * . Say the elements of the iterable object are <i>v<sub>0</sub></i>
		 * ,...,<i>v<sub>n-1</sub></i>. Each element of the sequence is either
		 * NULL (i.e., the expression with operator {@link #NULL}) or an
		 * expression of type <i>T</i>. The dense array write expression
		 * represents the result of starting with arg0 and then for each
		 * <i>i</i> for which <i>v<sub>i</sub></i> is non-NULL, setting the
		 * array element in position <i>i</i> to <i>v<sub>i</sub></i>. It is
		 * thus equivalent to a sequence of array write operations (which can be
		 * performed in any order since they are to distinct positions). It is
		 * included here to allow a dense representation of the array, which can
		 * have performance benefits, in particular constant-time lookup and
		 * modification (just like for regular concrete arrays).
		 * 
		 * @see #ARRAY_WRITE
		 * @see #DENSE_TUPLE_WRITE
		 */
		DENSE_ARRAY_WRITE,
		/**
		 * Operator representing the result of multiple writes to different
		 * components of a tuple. Similar to {@link #DENSE_ARRAY_WRITE}. Arg0 is
		 * an expression of {@link SymbolicTupleType}. Arg1 is an
		 * <code>{@link Iterable}&lt;? extends {@link SymbolicExpression}&gt;</code>
		 * . The writes to the components of the tuple are taken from arg1 in
		 * order. Entries which are NULL are ignored (as with arrays). The
		 * number of elements in arg1 may be less than the number of components
		 * in the tuple, in which case only those elements are used. If the
		 * length of arg1 is greater, the extra elements are ignored.
		 * 
		 * @see #DENSE_ARRAY_WRITE
		 */
		DENSE_TUPLE_WRITE,
		/**
		 * Operator for real number division. 2 arguments: arg0 the numerator,
		 * arg1 the denominator. Both must be symbolic expressions of
		 * {@link SymbolicRealType}. Result also has {@link SymbolicRealType}.
		 * 
		 * @see #INT_DIVIDE
		 */
		DIVIDE,
		/**
		 * Operator for comparison of two values for equality. Two arguments,
		 * both {@link NumericExpression}s. Result is a
		 * {@link BooleanExpression}.
		 * 
		 * @see #NEQ
		 */
		EQUALS,
		/**
		 * Operator for for existential quantification: &exist; <i>x</i> .
		 * <i>e</i>. 2 arguments. arg0 is a {@link SymbolicConstant} <i>x</i>,
		 * the bound variable. Arg1 is <i>e</i>, a {@link BooleanExpression}
		 * which may involve <i>x</i>. Result has boolean type.
		 * 
		 * @see #FORALL
		 */
		EXISTS,
		/**
		 * Operator for for universal quantification: &forall; <i>x</i> .
		 * <i>e</i>. 2 arguments. arg0 is a {@link SymbolicConstant} <i>x</i>,
		 * the bound variable. Arg1 is <i>e</i>, a {@link BooleanExpression}
		 * which may involve <i>x</i>. Result has boolean type.
		 * 
		 * @see #EXISTS
		 */
		FORALL,
		/**
		 * Operator for integer division. Two arguments, both
		 * {@link SymbolicExpression}s of {@link SymbolicIntegerType}. Arg0 is
		 * the numerator, arg1 the denominator. Result has
		 * {@link SymbolicIntegerType}. Result is obtained by rounding towards
		 * 0. Undefined behavior if denominator is not positive.
		 * 
		 * @see #DIVIDE
		 */
		INT_DIVIDE,
		/**
		 * Operator for a lambda expression, as in the lambda calculus: &lambda;
		 * <i>x</i> . <i>e</i>. Two arguments. Arg0 is a
		 * {@link SymbolicConstant} <i>x</i>, the bound variable. Arg1 is
		 * <i>e</i>, a {@link SymbolicExpression} possibly involving <i>x</i>.
		 * The result has {@link SymbolicFunctionType} and represents the
		 * function of one variable which, given <i>x</i> returns <i>e</i>.
		 */
		LAMBDA,
		/**
		 * Operator for getting the length of an array. Has 1 argument, arg0,
		 * which is the array expression, a {@link SymbolicExpression} of type
		 * {@link SymbolicArrayType}. Result has {@link SymbolicIntegerType}.
		 */
		LENGTH,
		/**
		 * Operator for a less-than expression: <i>x</i> &lt; <i>y</i>. Two
		 * arguments, both instances of {@link NumericExpression} with the same
		 * numeric type. Arg0 is <i>x</i>, arg1 is <i>y</i>. Result has boolean
		 * type.
		 * 
		 * @see #LESS_THAN_EQUALS
		 */
		LESS_THAN,
		/**
		 * Operator for a less-than-or-equals expression: <i>x</i> &le; <i>y</i>
		 * . Two arguments, both instances of {@link NumericExpression} with the
		 * same numeric type. Arg0 is <i>x</i>, arg1 is <i>y</i>. Result has
		 * boolean type.
		 * 
		 * @see #LESS_THAN
		 */
		LESS_THAN_EQUALS,
		/**
		 * The integer modulus operator. Takes 2 arguments, result represents
		 * <i>x</i> mod <i>y</i> (or <code>x%y</code> in C). Arg0 is <i>x</i>,
		 * arg1 is <i>y</i>. Both arguments and the result are
		 * {@link NumericExpression}s of {@link SymbolicIntegerType}. Undefined
		 * behavior if <i>y</i> is not positive.
		 * 
		 * @see #INT_DIVIDE
		 */
		MODULO,
		/**
		 * Operator for an expression representing the numerical product of
		 * symbolic expressions. Can have 1 or 2 arguments, like {@link #ADD}.
		 * Takes 1 or 2 arguments. If 1, the argument is an instance of
		 * <code>{@link Iterable}&lt;? extends
		 * {@link NumericExpression}&gt;</code> with at least one element; the
		 * {@link #MULTIPLY} expression represents the product of the elements
		 * in the collection. The elements of the collection must all have the
		 * same numeric (integer or real) type. If 2, then both arguments are
		 * {@link NumericExpression}s and have the same numeric (integer or
		 * real) type, and the {@link #MULTIPLY} expression represents the
		 * product of the two arguments. Result is also a
		 * {@link NumericExpression}.
		 * 
		 * @see #ADD
		 */
		MULTIPLY,
		/**
		 * Operator for numerical negation, i.e., <strong>- <i>x</i></strong>. 1
		 * argument, which is a {@link NumericExpression}. The result is a
		 * {@link NumericExpression} of the same type as that of the argument.
		 */
		NEGATIVE,
		/**
		 * Operator for comparison of two values for inequality. Two arguments,
		 * both symbolic expressions of the same type. Result is a
		 * {@link BooleanExpression}.
		 * 
		 * @see #EQUALS
		 */
		NEQ,
		/**
		 * Operator for logical negation ("not"). Takes one argument, a
		 * {@link BooleanExpression}. Result is a {@link BooleanExpression}.
		 * 
		 * @see #AND
		 * @see #OR
		 */
		NOT,
		/**
		 * Operator used to represent no symbolic expression in cases where
		 * Java's <code>null</code> is not acceptable. This is the only kind of
		 * {@link SymbolicExpression} that has a <code>null</code> type! Takes
		 * no arguments.
		 */
		NULL,
		/**
		 * Operator for an expression representing the conjunction of symbolic
		 * expressions of boolean type. Has 1 or 2 arguments, similar to
		 * {@link #ADD}. If 1, the argument is an
		 * <code>{@link Iterable}&lt;? extends
		 * {@link BooleanExpression}&gt;</code>. All symbolic expressions in the
		 * collection have boolean type. If there are 2 arguments, they are both
		 * {@link BooleanExpression}s. Result is also a
		 * {@link BooleanExpression}.
		 * 
		 * @see #AND
		 * @see #ADD
		 */
		OR,
		/**
		 * Operator for exponentiation, i.e., the raising of some number to some
		 * power: <i>x <sup>y</sup></i>. Takes two arguments: arg0 is the base
		 * <i>x</i>, arg1 is the exponent <i>y</i>. The exponent can be either a
		 * {@link NumericExpression} or an {@link IntObject}. In the latter
		 * case, the int must be non-negative.
		 */
		POWER,
		/**
		 * Operator for numerical subtraction: <i>x</i> &#8722; <i>y</i>. Two
		 * arguments, both {@link NumericExpression}s of the same type: arg0 is
		 * <i>x</i>, arg1 is <i>y</i>. Result is also a
		 * {@link NumericExpression} of the same type.
		 */
		SUBTRACT,
		/**
		 * Operator used to represent a symbolic constant. Takes one argument, a
		 * {@link StringObject}, which gives the name of the symbolic constant.
		 * Note that a symbolic constant can have any {@link SymbolicType},
		 * including a {@link SymbolicFunctionType}.
		 */
		SYMBOLIC_CONSTANT,
		/**
		 * A concrete tuple. The arguments are the components of the tuple.
		 */
		TUPLE,
		/**
		 * Operator for an expression representing the result of reading a
		 * component of a tuple. Takes two arguments: arg0 is the tuple
		 * expression, arg1 is an {@link IntObject} giving the index into the
		 * tuple.
		 * 
		 * @see #TUPLE_WRITE
		 */
		TUPLE_READ,
		/**
		 * Operator for an expression representing the result of modifying a
		 * single component of a tuple. Takes three arguments: arg0 is the
		 * original expression of {@link SymbolicTupleType}, arg1 is an
		 * {@link IntObject} specifying the index into the tuple, and arg2 is
		 * the expression that will be the new value for specified component.
		 * The result represents the tuple that is the same as arg0, except in
		 * component arg1, where the value is arg2.
		 * 
		 * @see #TUPLE_READ
		 * @see #DENSE_TUPLE_WRITE
		 */
		TUPLE_WRITE,
		/**
		 * Operator for extracting an element of a {@link SymbolicUnionType} to
		 * an element of a member type. Takes 2 arguments: arg0 is an
		 * {@link IntObject} giving the index of a member type of a union type;
		 * arg1 is a {@link SymbolicExpression} whose type is the union type.
		 * The resulting expression has type the specified member type. This
		 * essentially pulls the expression out of the union and casts it to the
		 * member type. If arg1 does not belong to the member type (as
		 * determined by a {@link #UNION_TEST} expression), the value of this
		 * expression is undefined.
		 */
		UNION_EXTRACT,
		/**
		 * Operator for injecting an element of a member type into a
		 * {@link SymbolicUnionType} that includes that member type. Takes 2
		 * arguments: arg0 is an {@link IntObject} giving the index of the
		 * member type of the union type; arg1 is a {@link SymbolicExpression}
		 * whose type is the member type. The union type itself is the type of
		 * the {@link #UNION_INJECT} expression.
		 */
		UNION_INJECT,
		/**
		 * Operator to determine whether an expression in a
		 * {@link SymbolicUnionType} is in the image of injection from a
		 * specified member type. Takes 2 arguments: arg0 is an
		 * {@link IntObject} giving the index of a member type of the union
		 * type; arg1 is a {@link SymbolicExpression} whose type is the union
		 * type. This is a boolean-valued expression whose value is
		 * <code>true</code> iff arg1 belongs to the specified member type of
		 * the union type.
		 */
		UNION_TEST
	}

	/**
	 * Returns the i-th argument (child) of the operator.
	 * 
	 * @param index
	 *            the index i
	 * @return the i-th argument
	 */
	SymbolicObject argument(int index);

	/**
	 * Returns the sequence of arguments as an {@link Iterable} object.
	 * 
	 * @return the argument sequence as an {@link Iterable}
	 */
	Iterable<? extends SymbolicObject> getArguments();

	/**
	 * A string representation appropriate for nesting in other expressions,
	 * typically by surrounding the normal string version with parentheses if
	 * necessary.
	 */
	String atomString();

	/**
	 * Is this the boolean "false" expression?
	 * 
	 * @return true iff this is the boolean expression "false".
	 */
	boolean isFalse();

	/**
	 * Is this the "NULL" symbolic expression? A NULL expression has operator
	 * {@link SymbolicOperator#NULL}, 0 arguments, and <code>null</code> type.
	 * 
	 * @return <code>true</code> iff the operator of this expression is
	 *         {@link SymbolicOperator#NULL}.
	 */
	boolean isNull();

	/**
	 * Is this a numeric expression, i.e., does this have integer or real type?
	 * If true, this may be safely cast to {@link NumericExpression}.
	 * 
	 * @return true iff type is integer or real
	 */
	boolean isNumeric();

	/**
	 * Is this the integer or real 1 expression?
	 * 
	 * @return true iff this is the integer 1 or the real 1
	 */
	boolean isOne();

	/**
	 * Is this the boolean "true" expression?
	 * 
	 * @return true iff this is the boolean expression "true".
	 */
	boolean isTrue();

	/**
	 * Is this the integer or real 0 expression?
	 * 
	 * @return true iff this is the integer 0 or the real 0
	 */
	boolean isZero();

	/**
	 * The number of arguments (children) of this symbolic expression.
	 * 
	 * @return number of arguments
	 */
	int numArguments();

	/**
	 * The operator of this symbolic expression.
	 * 
	 * @return the operator of the symbolic expression
	 */
	SymbolicOperator operator();

	/**
	 * Returns the type of this symbolic expression.
	 * 
	 * @return the {@link SymbolicType} of this expression
	 */
	SymbolicType type();

}
