package edu.udel.cis.vsl.abc.ast.node.IF.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;

/**
 * This represents an OpenMP reduction clause. The syntax of a reduction clause
 * is as follows:
 * 
 * <pre>
 * reduction(reduction-identifier:list)
 * where reduction-identifier is either an identifier or
 * one of the following operators:
 * +, -, *, &, |, ^, && and ||.
 * </pre>
 * 
 * @author Manchun Zheng
 * 
 */
public interface OmpReductionNode extends ASTNode {

	/**
	 * The kind of this reduction clause, either
	 * <ul>
	 * <li>OPERATOR if the reduction-identifier is one of the following:+, -, *,
	 * &, |, ^, && and ||;</li> or
	 * <li>FUNCTION if the reduction-identifier is an identifier.</li>
	 * </ul>
	 * 
	 * @author Manchun Zheng
	 * 
	 */
	public enum OmpReductionNodeKind {
		FUNCTION, OPERATOR
	}

	/**
	 * Returns the kind of this reduction clause.
	 * 
	 * @return the kind of this reduction clause.
	 */
	OmpReductionNodeKind ompReductionOperatorNodeKind();

	/**
	 * Returns the list of variables associated with this clause.
	 * 
	 * @return the list of variables associated with this clause.
	 */
	SequenceNode<IdentifierExpressionNode> variables();
}
