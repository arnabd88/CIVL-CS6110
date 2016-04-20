package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

/**
 * An interface indicating that this object can be used as an argument to the C
 * <code>sizeof</code> operator. I.e., this object is either an expression or a
 * type.
 * 
 * @see ExpressionNode
 * @see TypeNode
 * 
 * @author siegel
 * 
 */
public interface SizeableNode extends ASTNode {

	/**
	 * If this is a type node, returns the conceptual C type associated to the
	 * type node; if this is an expression node, returns the converted type
	 * associated to the expression.
	 * 
	 * @return the C type defined by this node
	 */
	Type getType();

	@Override
	SizeableNode copy();

}
