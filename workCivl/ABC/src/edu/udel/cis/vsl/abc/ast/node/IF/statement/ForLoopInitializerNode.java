package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * <p>
 * A marker interface indicating this construct can be used as the first clause
 * in a <code>for</code> loop. This clause can be either an expression or a
 * declaration list.
 * </p>
 * 
 * 
 * <p>
 * From C11 Sec. 6.8.5.3: "The declaration part of a for statement shall only
 * declare identifiers for objects having storage class auto or register."
 * </p>
 * 
 * @author siegel
 * 
 * @see DeclarationListNode
 * @see ExpressionNode
 * 
 */
public interface ForLoopInitializerNode extends ASTNode {

	@Override
	ForLoopInitializerNode copy();

}
