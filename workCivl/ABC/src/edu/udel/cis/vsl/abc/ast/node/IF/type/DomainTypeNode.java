package edu.udel.cis.vsl.abc.ast.node.IF.type;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * Represents use of the CIVL-C domain type, either "$domain" alone, or one of
 * the sub-types "$domain(n)" for some positive integer constant n.
 * 
 * @author siegel
 * 
 */
public interface DomainTypeNode extends TypeNode {

	/**
	 * Returns the integer constant dimention of the domain if present, else
	 * returns <code>null</code>
	 * 
	 * @return the dimension expression or <code>null</code>
	 */
	ExpressionNode getDimension();

}
