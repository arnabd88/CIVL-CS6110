package edu.udel.cis.vsl.abc.ast.node.IF.expression;

/**
 * Represents the CIVL-C built-in variable <code>$self</code>, which has type
 * <code>$scope</code> and evaluates to the dynamic scope in which the variable
 * is being evaluated.
 * 
 * @author siegel
 * 
 */
public interface SelfNode extends ConstantNode {

	@Override
	SelfNode copy();
}
