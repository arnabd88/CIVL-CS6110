package edu.udel.cis.vsl.abc.ast.node.IF.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;

/**
 * This represents an OpenMP declarative directive, which can only be placed in
 * a declarative context. Currently, only <code>threadprivate</code> is
 * supported.
 * 
 * @author Manchun Zheng
 * 
 */
public interface OmpDeclarativeNode extends OmpNode, BlockItemNode {

	/**
	 * The kind of an OpenMP declarative pragma.
	 * 
	 * @author Manchun Zheng
	 * 
	 */
	public enum OmpDeclarativeNodeKind {
		REDUCTION, SIMD, TARGET, THREADPRIVATE
	}

	/**
	 * The kind of this OpenMP declarative node.
	 * 
	 * @return the declarative kind of this OpenMP declarative node.
	 */
	OmpDeclarativeNodeKind ompDeclarativeNodeKind();

	/**
	 * Updates the list of variable declared by this directive.
	 * 
	 * @param list
	 *            The list of identifier expression nodes.
	 */
	void setList(SequenceNode<IdentifierExpressionNode> list);

	/**
	 * Returns a sequence node of identifier expression nodes:
	 * <ul>
	 * <li><code>threadprivate(x, y, z, ...)</code>: a non-empty sequence node</li>
	 * <li><code>threadprivate()</code>: an empty sequence node</li>
	 * </ul>
	 * 
	 * @return the list of variables in this declarative construct.
	 */
	SequenceNode<IdentifierExpressionNode> variables();
}
