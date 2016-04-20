package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

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

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = new HashSet<>();

		if (elements != null) {
			for (Expression element : elements) {
				Set<Variable> elementResult = element
						.variableAddressedOf(scope);

				if (elementResult != null)
					result.addAll(elementResult);
			}
		}
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = new HashSet<>();

		if (elements != null) {
			for (Expression element : elements) {
				Set<Variable> elementResult = element.variableAddressedOf();

				if (elementResult != null)
					result.addAll(elementResult);
			}
		}
		return result;
	}

	@Override
	public LiteralKind literalKind() {
		return LiteralKind.ARRAY;
	}

}
