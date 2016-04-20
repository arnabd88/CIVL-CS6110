package edu.udel.cis.vsl.abc.ast.node.IF.expression;

/**
 * A node representing one of the two CIVL-C constant expressions of type
 * <code>$scope</code>: <code>$here</code> (the dynamic scope in which the
 * expression is evaluated), or <code>$root</code> (representing the root
 * dynamic scope).
 * 
 * @author siegel
 * 
 */
public interface HereOrRootNode extends ConstantNode {

	@Override
	HereOrRootNode copy();

	/**
	 * Is this <code>$here</code>?
	 * 
	 * @return <code>true</code> iff this is <code>$here</code>
	 */
	boolean isHereNode();

	/**
	 * Is this <code>$root</code>?
	 * 
	 * @return <code>true</code> iff this is <code>$root</code>
	 */
	boolean isRootNode();
}
