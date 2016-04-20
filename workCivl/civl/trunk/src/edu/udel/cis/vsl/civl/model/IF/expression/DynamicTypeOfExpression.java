/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

/**
 * A "DynamicTypeOf" expression. Such an expression has the form
 * DynamicTypeOf(t), where t is a (static) CIVL type. The type of this
 * expression is {@link CIVLDynamicType}. When evaluated, it returns the dynamic
 * type determined by the current state and the given static type. (This assumes
 * extent expressions are stored in array types.) For example, if <code>t</code>
 * is the static type <code>struct foo { double a[n]; }</code> from the source
 * code above, then <code>DynamicTypeOf(t)</code>, evaluated in the state that
 * arises at that point in the source code, will yield the symbolic type which
 * is a record type with one field which is an array of doubles of length 2. Now
 * you can store that dynamic type in a variable if you want to save it.
 * 
 * @author siegel
 * 
 */
public interface DynamicTypeOfExpression extends Expression {

	/**
	 * @return The type argument
	 */
	CIVLType getType();

}
