package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.ArrayList;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

public class CommonArrayLiteralExpression extends CommonExpression implements
		ArrayLiteralExpression {

	private Expression[] elements;

	public CommonArrayLiteralExpression(CIVLSource source, CIVLType type,
			ArrayList<Expression> elements) {
		super(source);
		this.elements = new Expression[elements.size()];
		elements.toArray(this.elements);
		this.setExpressionType(type);
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ARRAY_LITERAL;
	};

	@Override
	public String toString() {
		String result = "{";

		if (elements != null) {
			for (Expression element : elements) {
				result += element.toString() + ", ";
			}
			result = result.substring(0, result.length() - 2);
		}
		result += "}";
		return result;
	}

	@Override
	public Expression[] elements() {
		return this.elements;
	}

	@Override
	public void setElements(Expression[] elements) {
		this.elements = elements;
	}

	@Override
	public CIVLArrayType arrayType() {
		assert this.expressionType instanceof CIVLArrayType;
		return (CIVLArrayType) this.expressionType;
	}

	@Override
	public CIVLType elementType() {
		return this.arrayType().elementType();
	}

	// @Override
	// public int id() {
	// return this.id;
	// }
	//
	// @Override
	// public void setId(int id) {
	// this.id = id;
	// }

}
