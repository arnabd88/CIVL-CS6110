/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
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
	protected boolean hasDerefs;
	protected boolean purelyLocal = false;

	/**
	 * @return true iff the expression has at least one dereferences
	 */
	public boolean hasDerefs() {
		return hasDerefs;
	}

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

	@Override
	public void calculateDerefs() {
		this.hasDerefs = false;
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {

	}

	@Override
	public boolean isPurelyLocal() {
		return this.purelyLocal;
	}

	@Override
	public void purelyLocalAnalysis() {
		this.purelyLocal = !this.hasDerefs;
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {

	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		return null;
	}

}
