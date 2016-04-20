/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A cast of an expression to a different type.
 * 
 * @author zirkel
 * 
 */
public class CommonDynamicTypeOfExpression extends CommonExpression implements
		DynamicTypeOfExpression {

	private CIVLType type;

	public CommonDynamicTypeOfExpression(CIVLSource source, CIVLType myType,
			CIVLType type) {
		super(source, null, null, myType);
		this.type = type;
	}

	@Override
	public CIVLType getType() {
		return type;
	}

	@Override
	public String toString() {
		return "DynamicTypeOf(" + type + ") ";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DYNAMIC_TYPE_OF;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		DynamicTypeOfExpression that = (DynamicTypeOfExpression) expression;

		return this.type.equals(that.getType());
	}

}
