package edu.udel.cis.vsl.abc.ast.node.IF.declaration;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;

/**
 * <p>
 * A marker interface for any node that can be used as an initializer. An
 * initializer is used in a declaration to give an initial value to an
 * identifier.
 * </p>
 * 
 * <p>
 * There are two kinds of initializers: a simple expression (used to initialize
 * scalar variables) and compound initializers (used to initialize arrays,
 * structs, and unions).
 * </p>
 * 
 * @author siegel
 * 
 */
public interface InitializerNode extends ASTNode {

	@Override
	InitializerNode copy();

	/**
	 * Returns true iff this expression does not contain side effects.
	 * 
	 * @param errorsAreSideEffects
	 *            Whether to consider potential errors (division by 0, array
	 *            index out of bounds, etc.) as side effects.
	 * @return true iff this expression does not contain side effects
	 */
	boolean isSideEffectFree(boolean errorsAreSideEffects);

}
