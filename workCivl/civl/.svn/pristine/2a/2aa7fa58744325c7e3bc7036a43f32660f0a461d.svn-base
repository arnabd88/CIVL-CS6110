/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.common.CommonSourceable;

/**
 * The parent of all expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public abstract class CommonExpression extends CommonSourceable implements
		Expression {

	private Scope expressionScope = null;
	protected CIVLType expressionType = null;

	/**
	 * The parent of all expressions.
	 */
	public CommonExpression(CIVLSource source) {
		super(source);
	}

	/**
	 * @return The highest scope accessed by this expression. Null if no
	 *         variables accessed.
	 */
	public Scope expressionScope() {
		return expressionScope;
	}

	/**
	 * @param expressionScope
	 *            The highest scope accessed by this expression. Null if no
	 *            variables accessed.
	 */
	public void setExpressionScope(Scope expressionScope) {
		this.expressionScope = expressionScope;
	}

	@Override
	public CIVLType getExpressionType() {
		return expressionType;
	}

	/**
	 * 
	 * @param expressionType
	 *            The type resulting from this expression.
	 */
	public void setExpressionType(CIVLType expressionType) {
		this.expressionType = expressionType;
	}

}
