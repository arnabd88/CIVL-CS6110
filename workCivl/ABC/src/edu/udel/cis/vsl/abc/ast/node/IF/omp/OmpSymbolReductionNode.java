package edu.udel.cis.vsl.abc.ast.node.IF.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;

/**
 * This represents an OpenMP reduction clause with the reduction operator being
 * one of the following operators: <code>+</code>,<code>-</code>,<code>*</code>,
 * <code>&</code>,<code>|</code>,<code>^</code>,<code>&&</code>, and
 * <code>||</code>.
 * 
 * @author Manchun Zheng
 * 
 */
public interface OmpSymbolReductionNode extends OmpReductionNode {
	/**
	 * Returns the operator of this node.
	 * 
	 * @return the operator.
	 */
	Operator operator();
}
