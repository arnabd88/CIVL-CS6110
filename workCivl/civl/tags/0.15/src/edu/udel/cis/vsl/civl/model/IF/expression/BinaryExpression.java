/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * A binary operation.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface BinaryExpression extends Expression {

	/**
	 * This defines all CIVL binary operators: <br>
	 * 
	 * <ui> <li>AND: <code>&&</code> (logical and);</li> <li>LEFT_SHIFT:
	 * <code><</code> (bitwise left shift);</li> <li>RIGHT_SHIFT:
	 * <code>>></code> (bitwise right shift);</li> <li>BITAND: <code>&</code>
	 * (bitwise and);</li> <li>BITCOMPLEMENT: <code>~</code> (bitwise
	 * complement);</li> <li>BITOR: <code>|</code> (bitwise or);</li> <li>
	 * BITXOR: <code>^</code> (bitwise xor);</li> <li>DIVIDE: <code>/</code>
	 * (division);</li> <li>EQUAL: <code>==</code> (equal to);</li> <li>IMPLIES:
	 * <code></code> (implication);</li> <li>LESS_THAN: <code><</code> (less
	 * than);</li> <li>LESS_THAN_EQUAL: <code><=</code> (less than or equal to);
	 * </li> <li>MINUS: <code>-</code> (subtraction);</li> <li>MODULO:
	 * <code>%</code> (modulo);</li> <li>NOT_EQUAL: <code>!=</code> (not equal
	 * to);</li> <li>OR: <code>||</code> (logical or);</li> <li>PLUS:
	 * <code>+</code> (addition);</li> <li>POINTER_ADD: <code>+</code> (pointer
	 * addition);</li> <li>POINTER_SUBTRACT: <code>-</code> (pointer
	 * subtraction);</li> <li>TIMES: <code>*</code> (multiplication);</li> </ui>
	 * 
	 * @author Manchun Zheng (zmanchun)
	 * 
	 */
	public enum BINARY_OPERATOR {
		AND,
		BITAND,
		BITCOMPLEMENT,
		BITOR,
		BITXOR,
		DIVIDE,
		EQUAL,
		IMPLIES,
		LESS_THAN,
		LESS_THAN_EQUAL,
		MINUS,
		MODULO,
		NOT_EQUAL,
		OR,
		PLUS,
		POINTER_ADD,
		POINTER_SUBTRACT,
		SHIFTLEFT,
		SHIFTRIGHT,
		TIMES
	};

	/**
	 * @return The left operand.
	 */
	Expression left();

	/**
	 * @return The binary operator
	 */
	BINARY_OPERATOR operator();

	/**
	 * @return The right operand.
	 */
	Expression right();
}
