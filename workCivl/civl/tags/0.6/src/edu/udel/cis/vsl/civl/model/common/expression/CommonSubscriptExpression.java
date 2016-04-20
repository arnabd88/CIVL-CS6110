/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;

/**
 * a[i], where "a" is an array and "i" is an expression evaluating to an
 * integer.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonSubscriptExpression extends CommonExpression implements
		SubscriptExpression {

	private LHSExpression array;
	private Expression index;

	/**
	 * a[i], where "a" is an array and "i" is an expression evaluating to an
	 * integer.
	 * 
	 * @param array
	 *            An expression evaluating to an array.
	 * @param index
	 *            An expression evaluating to an integer.
	 */
	public CommonSubscriptExpression(CIVLSource source, LHSExpression array,
			Expression index) {
		super(source);
		this.array = array;
		this.index = index;
	}

	/**
	 * @return The expression for the array.
	 */
	public LHSExpression array() {
		return array;
	}

	/**
	 * @return The expression for the index.
	 */
	public Expression index() {
		return index;
	}

	/**
	 * @param array
	 *            The expression for the array.
	 */
	public void setArray(LHSExpression array) {
		this.array = array;
	}

	/**
	 * @param index
	 *            The expression for the index.
	 */
	public void setIndex(Expression index) {
		this.index = index;
	}

	@Override
	public String toString() {
		return array + "[" + index + "]";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.SUBSCRIPT;
	}

	@Override
	public void calculateDerefs() {
		this.array.calculateDerefs();
		this.index.calculateDerefs();
		this.hasDerefs = this.array.hasDerefs() || this.index.hasDerefs();
	}

	@Override
	public void setPurelyLocal(boolean pl) {
		this.purelyLocal = pl;
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.array.purelyLocalAnalysisOfVariables(funcScope);
		this.index.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		if (!this.purelyLocal)
			return;

		if (this.hasDerefs) {
			this.purelyLocal = false;
			return;
		}

		this.array.purelyLocalAnalysis();
		this.index.purelyLocalAnalysis();
		this.purelyLocal = this.array.isPurelyLocal()
				&& this.index.isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (index == oldExpression) {
			index = newExpression;
			return;
		}
		index.replaceWith(oldExpression, newExpression);
		array.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newIndex = index.replaceWith(oldExpression, newExpression);
		CommonSubscriptExpression result = null;

		if (newIndex != null) {
			result = new CommonSubscriptExpression(this.getSource(), array,
					newIndex);
		} else {
			Expression newArray = array.replaceWith(oldExpression,
					newExpression);

			if (newArray != null)
				result = new CommonSubscriptExpression(this.getSource(),
						(LHSExpression) newArray, index);
		}

		if (result != null)
			result.setExpressionType(expressionType);

		return result;
	}
}
