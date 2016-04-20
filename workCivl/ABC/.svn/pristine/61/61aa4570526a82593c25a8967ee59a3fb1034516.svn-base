package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

/**
 * An composite event 
 * @author Manchun Zheng
 *
 */
public interface CompositeEventNode extends DependsEventNode {
	/**
	 * The operator of a composite event
	 * 
	 * @author Manchun Zheng
	 *
	 */
	public enum EventOperator {
		UNION, DIFFERENCE, INTERSECT
	}

	/**
	 * The left operand of the composite event
	 * 
	 * @return
	 */
	DependsEventNode getLeft();

	/**
	 * The right operand of the composite event
	 * 
	 * @return
	 */
	DependsEventNode getRight();

	/**
	 * the operatore of this composite event
	 * 
	 * @return
	 */
	EventOperator eventOperator();

	@Override
	CompositeEventNode copy();
}
