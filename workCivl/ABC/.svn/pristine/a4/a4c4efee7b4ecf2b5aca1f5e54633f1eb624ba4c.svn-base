package edu.udel.cis.vsl.abc.ast.node.IF.expression;

/**
 * <p>
 * A node that represents an expression built using an operator.
 * </p>
 * 
 * <p>
 * The most common type of expression is an expression that involves an operator
 * and some number of operands. The operands are the children of this AST node.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface OperatorNode extends ExpressionNode {

	/**
	 * An enumerated type for all the different operators that can occur in an
	 * {@link OperatorNode}. Some operators are not included here because they
	 * have their own class. In particular, any operator that results in a
	 * left-hand-side expression has its own class.
	 * 
	 * @author siegel
	 * 
	 */
	public enum Operator {
		/**
		 * The unary address-of operator <code>&</code>, as in <code>&e</code>,
		 * which returns a pointer to the object specified by its argument
		 * <code>e</code>.
		 */
		ADDRESSOF,
		/**
		 * The standard binary assignment operator <code>=</code>, as in
		 * <code>lhs=rhs</code>.
		 */
		ASSIGN,
		/**
		 * The CIVL-C "big-O" operator <code>$O</code>, as in
		 * <code>$O(h*h)</code>, which is used to specify the asymptotic
		 * complexity of an expression as a parameter approaches zero.
		 */
		BIG_O,
		/**
		 * The bitwise and binary operator <code>&</code>, as in
		 * <code>e&f</code>, which performs the bit-wise and operation on the
		 * corresponding bits of the two integer values.
		 */
		BITAND,
		/**
		 * The bit-wise and assignment operator <code>&=</code>, as in
		 * <code>lhs&=rhs</code>, which performs the bit-wise and operation on
		 * the two arguments and stores the result in the <code>lhs</code>.
		 */
		BITANDEQ,
		/**
		 * The bit-wise complement operator <code>~</code>, as in
		 * <code>~e</code>, which negates each bit in an integer value.
		 */
		BITCOMPLEMENT,
		/**
		 * The bit-wise inclusive or operator <code>|</code>, as in
		 * <code>e|f</code>, which performs the logical or operation on the
		 * corresponding bits of two integer values.
		 */
		BITOR,
		/**
		 * The bit-wise inclusive or assignment operator <code>|=</code>, as in
		 * <code>lhs|=rhs</code>, which performs bit-wise or on the two
		 * arguments and stores the result in the <code>lhs</code>.
		 */
		BITOREQ,
		/**
		 * The bit-wise exclusive or operator <code>^</code>, as in
		 * <code>e^f</code>, which performs the exclusive-or operation on the
		 * respective bits of two integer values.
		 */
		BITXOR,
		/**
		 * The bit-wise exclusive or assignment operator <code>^=</code>, which
		 * performs the bit-wise exclusive or operation on the two arguments and
		 * stores the result in the left-hand-side argument.
		 */
		BITXOREQ,
		/**
		 * The comma operator <code>,</code>, as in <code>e,f</code> which
		 * evaluates <code>e</code> and then <code>f</code>, and returns the
		 * result of evaluating <code>f</code>. Useful only if <code>e</code>
		 * has side-effects.
		 */
		COMMA,
		/**
		 * The ternary if-then-else operator <code>?</code>, as in
		 * <code>e1 ? e2 : e3</code>. Evaluates <code>e1</code> and converts to
		 * boolean; if result is <code>true</code>, evaluates and returns
		 * <code>e2</code>, else evaluates and returns <code>e2</code>.
		 */
		CONDITIONAL,
		/**
		 * The pointer dereference unary operator <code>*</code>, as in
		 * <code>*e</code>, which returns the value stored in the memory
		 * location pointed to by <code>e</code>.
		 */
		DEREFERENCE,
		/**
		 * The numeric division operator <code>/</code>, as in <code>e/f</code>,
		 * used for integer or floating-point division.
		 */
		DIV,
		/**
		 * The numeric division assignment operator <code>/=</code>, as in
		 * <code>lhs/=rhs</code>, which evaluates <code>lhs/rhs</code> and
		 * stores the result in <code>lhs</code>.
		 */
		DIVEQ,
		/**
		 * The equality operator <code>==</code>, as in <code>e==f</code>, which
		 * returns the integer 1 if the two arguments are equal, else returns
		 * the integer 0. The arguments must have scalar type.
		 */
		EQUALS,
		/**
		 * The greater-than relational operator, as in <code>e>f</code>, which
		 * returns the integer 1 if <code>e</code> is greater than
		 * <code>f</code>, else returns 0.
		 */
		GT,
		/**
		 * The greater-than-or-equal-to relational operator, as in
		 * <code>e>=f</code>, which returns the integer 1 if <code>e</code> is
		 * greater than or equal to <code>f</code>, else returns 0.
		 */
		GTE,
		/**
		 * The CIVL-C "remote" operator <code>#</code>, as in
		 * <code>expr0 # expr</code>.
		 */
		HASH,
		/**
		 * The CIVL-C logical implication operator <code>=></code>, as in
		 * <code>e=>f</code> which is equivalent to <code>(!e)||f</code>.
		 */
		IMPLIES,
		/**
		 * The logical and operator <code>&&</code>, as in <code>e&&f</code>,
		 * which returns the integer 1 if <code>e</code> and <code>f</code> are
		 * both true (not 0), else returns 1. This is a short-circuit operator,
		 * so if <code>e</code> is false, <code>f</code> is not evaluated.
		 */
		LAND,
		/**
		 * The logical or operator <code>||</code>, as in <code>e||f</code>,
		 * which returns the integer 1 if <code>e</code> or <code>f</code> is
		 * true (not 0), else returns 1. This is a short-circuit operator, so if
		 * <code>e</code> is true, <code>f</code> is not evaluated.
		 */
		LOR,
		/**
		 * The less-than relational operator, as in <code>e&lt;f</code>, which
		 * returns the integer 1 if <code>e</code> is less than <code>f</code>,
		 * else returns 0.
		 */
		LT,
		/**
		 * The less-than-or-equal-to relational operator, as in
		 * <code>e <= f</code>, which returns the integer 1 if <code>e</code> is
		 * less than or equal to <code>f</code>, else returns 0.
		 */
		LTE,
		/**
		 * The binary subtraction operator <code>-</code>, as in
		 * <code>e-f</code>. If both operands are numeric, returns the numeric
		 * difference. Also used in the case where <code>e</code> has pointer
		 * type and <code>f</code> is an integer (in which case the result is a
		 * pointer of the same type as <code>e</code>), and in the case where
		 * <code>e</code> and <code>f</code> are both pointers of the same type,
		 * in which case the result is an integer.
		 */
		MINUS,
		/**
		 * The subtraction assignment operator <code>-=</code>, as in
		 * <code>e-=f</code>, which performs subtraction <code>e-f</code> and
		 * stores the result in <code>e</code>.
		 */
		MINUSEQ,
		/**
		 * The integer modulus operator <code>%</code>, as in <code>e%f</code>.
		 */
		MOD,
		/**
		 * The integer modulus assignment operator <code>%=</code>, which stores
		 * the result of <code>e%f</code> in <code>e</code>.
		 */
		MODEQ, // %= integer modulus assignment
		/**
		 * The not-equals operator <code>!=</code>, as in <code>e!=f</code>,
		 * which returns the integer 1 if the two arguments are not equal, else
		 * returns the integer 0. The arguments must have scalar type.
		 */
		NEQ,
		/**
		 * The logical not operator <code>!</code>, as in <code>!e</code> which
		 * returns the integer 1 if <code>e</code> is zero, else returns 0.
		 */
		NOT,
		/**
		 * The binary addition operator <code>+</code>, as in <code>e+f</code>.
		 * If both arguments are numeric, the result is the numeric sum; if one
		 * argument is a pointer and the other an integer, the result is a
		 * pointer of the same type as the pointer operand.
		 */
		PLUS,
		/**
		 * The addition assignment operator <code>+=</code> as in
		 * <code>lhs+=rhs</code>. Stores the result of <code>lhs+rhs</code> in
		 * <code>lhs</code>.
		 */
		PLUSEQ,
		/**
		 * The post-decrement operator <code>--</code>, as in <code>e--</code>,
		 * which subtracts one from e, storing the result in e, and returns the
		 * original value of e.
		 */
		POSTDECREMENT,
		/**
		 * The post-increment operator <code>++</code>, as in <code>e++</code>,
		 * which adds one to e, storing the result in e, and returns the
		 * original value of e.
		 */
		POSTINCREMENT,
		/**
		 * The pre-decrement operator <code>--</code>, as in <code>--e</code>,
		 * which subtracts one from e, storing the result in e, and returns the
		 * decremented result.
		 */
		PREDECREMENT,
		/**
		 * The pre-increment operator <code>++</code>, as in <code>++e</code>,
		 * which adds one to e, storing the result in e, and returns the
		 * incremented result.
		 */
		PREINCREMENT,
		/**
		 * The shift-left operator <code> << </code>, as in <code>e << f</code>,
		 * which returns the integer obtained by shifting the bits comprising
		 * integer <code>e</code> <code>f</code> units to the left.
		 */
		SHIFTLEFT,
		/**
		 * The shift left assignment operator <code> <<= </code>, as in
		 * <code>e <<= f</code>, which stores in <code>e</code> the result of
		 * <code>e << f</code>.
		 */
		SHIFTLEFTEQ,
		/**
		 * The shift-right operator <code> >> </code>, as in <code>e >> f</code>
		 * , which returns the integer obtained by shifting the bits comprising
		 * integer <code>e</code> <code>f</code> units to the right.
		 */
		SHIFTRIGHT,
		/**
		 * The shift right assignment operator <code> >>= </code>, as in
		 * <code>e >>= f</code>, which stores in <code>e</code> the result of
		 * <code>e >> f</code>.
		 */
		SHIFTRIGHTEQ,
		/**
		 * The array subscript operator <code>[]</code>, as in <code>a[i]</code>
		 * , which returns the element in position <code>i</code> of array
		 * <code>a</code>.
		 */
		SUBSCRIPT,
		/**
		 * The multiplication operator <code>*</code>, as in <code>e*f</code>.
		 */
		TIMES,
		/**
		 * The multiplication assignment operator <code>*=</code>, as in
		 * <code>e*=f</code>, which stores in <code>e</code> the result of
		 * <code>e*f</code>.
		 */
		TIMESEQ,
		/**
		 * The unary minus operator <code>-</code>, as in <code>-e</code>, which
		 * return the numeric negation of the number <code>e</code>.
		 */
		UNARYMINUS,
		/**
		 * The unary plus operator <code>+</code>, as in <code>+e</code>, which
		 * returns <code>e</code>.
		 */
		UNARYPLUS,
		/**
		 * ACSL Valid operator
		 */
		VALID
	};

	/**
	 * Returns the operator of this expression.
	 * 
	 * @return the operator
	 */
	Operator getOperator();

	/**
	 * Sets the operator of this expression.
	 * 
	 * @param operator
	 *            the operator
	 */
	void setOperator(Operator operator);

	/**
	 * Returns the number of arguments (operands) in this operator expression.
	 * 
	 * @return the number of arguments
	 */
	int getNumberOfArguments();

	/**
	 * Returns the index-th argument, indexed from 0.
	 * 
	 * @return the index-th argument (operand) of this expression
	 */
	ExpressionNode getArgument(int index);

	/**
	 * Sets the index-th argument of this expression to be the given expression
	 * 
	 * @param index
	 *            nonnegative integer in appropriate range for the operator
	 * @param value
	 *            expression to be made the operand in that index
	 */
	void setArgument(int index, ExpressionNode value);

	@Override
	OperatorNode copy();

}
