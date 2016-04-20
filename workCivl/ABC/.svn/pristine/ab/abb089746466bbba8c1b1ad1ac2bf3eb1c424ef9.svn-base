package edu.udel.cis.vsl.abc.ast.node.IF.type;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * GNU C language reference 6.6 Referring to a Type with typeof
 * 
 * Another way to refer to the type of an expression is with typeof. The syntax
 * of using of this keyword looks like sizeof, but the construct acts
 * semantically like a type name defined with typedef.
 * 
 * There are two ways of writing the argument to typeof: with an expression or
 * with a type. Here is an example with an expression:
 * 
 * typeof (x[0](1)) This assumes that x is an array of pointers to functions;
 * the type described is that of the values of the functions.
 * 
 * Here is an example with a typename as the argument:
 * 
 * typeof (int *) Here the type described is that of pointers to int.
 * 
 * @author zmanchun
 *
 */
public interface TypeofNode extends TypeNode {
	boolean hasExpressionOperand();

	ExpressionNode getExpressionOperand();

	TypeNode getTypeOperand();
}
