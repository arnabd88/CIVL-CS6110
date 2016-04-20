/**
 * 
 */
package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;

/**
 * A CIVL-C quantified expression, e.g.,
 * 
 * <pre>
 * forall {int x | x > 0} x > -1
 * </pre>
 * 
 * which means "for all ints x for which x&gt;0, x&gt;-1". As can be seen in
 * this example, the CIVL-C syntax allows one to restrict the domain of x to a
 * subset of the domain of its type. It is equivalent to "for all ints x, x&gt;0
 * implies x&gt;-1" but can be more convenient and also enable optimizations.
 * 
 * @author zirkel
 * 
 */
public interface QuantifiedExpressionNode extends ExpressionNode {

	/**
	 * An enumerated type for the different quantifiers.
	 * 
	 * @author siegel
	 * 
	 */
	enum Quantifier {
		/**
		 * The universal quantifier "for all".
		 */
		FORALL,
		/**
		 * The existential quantifier "there exists".
		 */
		EXISTS,
		/**
		 * A special case of the universal quantifier for expression of uniform
		 * continuity.
		 */
		UNIFORM;
	}

	/**
	 * Returns the quantifier.
	 * 
	 * @return The quantifier used by this quantifier expression.
	 */
	Quantifier quantifier();

	/**
	 * Returns the declaration of the bound variable.
	 * 
	 * @return The bound variable declaration
	 */
	VariableDeclarationNode variable();

	/**
	 * Determines if this quantifier expression has the following alternative
	 * form: the quantified variable has integer type, and the restriction has
	 * the form " <code>i=lo..hi</code>", a special notation indicating
	 * <code>lo</code>&le; <code>i</code>&le;<code>hi</code>.
	 * 
	 * 
	 * @return <code>true</code> iff the bound variable in this expression is
	 *         specified to have a range (e.g. i=0..n).
	 */
	boolean isRange();

	/**
	 * Returns the predicate which specifies the restriction on the domain of
	 * the bound variable.
	 * 
	 * @return the boolean expression involving the bound variable which
	 *         restricts the domain of that variable, or <code>null</code> if
	 *         {@link #isRange()} is <code>true</code>
	 */
	ExpressionNode restriction();

	/**
	 * If this expression has an integer range restriction, returns the lower
	 * bound of the range, else returns <code>null</code>
	 * 
	 * @return If the bound variable in this expression is specified to have a
	 *         range, the lower end of the range (e.g., 0 in i=0..n). Returns
	 *         <code>null</code> iff {@link #isRange()} is <code>false</code>
	 */
	ExpressionNode lower();

	/**
	 * If this expression has an integer range restriction, returns the upper
	 * bound of the range, else returns <code>null</code>
	 * 
	 * @return If the bound variable in this expression is specified to have a
	 *         range, the upper bound of the range (e.g., n in i=0..n). Returns
	 *         <code>null</code> iff {@link #isRange()} is <code>false</code>
	 */
	ExpressionNode upper();

	/**
	 * The quantified expression.
	 * 
	 * @return The quantified expression.
	 */
	ExpressionNode expression();

}
