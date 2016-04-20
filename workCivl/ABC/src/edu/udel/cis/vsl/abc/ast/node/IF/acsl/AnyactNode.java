package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

/**
 * This represents ACSL-CIVLC <code>\anyact</code> action to be used in
 * <code>depends</code> contract clauses.
 * 
 * @author Manchun Zheng
 *
 */
public interface AnyactNode extends DependsEventNode {

	@Override
	AnyactNode copy();
}
