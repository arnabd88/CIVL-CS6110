package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonArrayLiteralExpression extends CommonExpression implements
		ArrayLiteralExpression {

	private Expression[] elements;

	public CommonArrayLiteralExpression(CIVLSource source, CIVLType arrayType,
			List<Expression> elements) {
		super(source);
		this.elements = new Expression[elements.size()];
		elements.toArray(this.elements);
		this.setExpressionType(arrayType);
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ARRAY_LITERAL;
	};

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();
		CIVLType eleType = this.arrayType().elementType();
		boolean first;

		if (eleType instanceof CIVLPrimitiveType) {
			if (((CIVLPrimitiveType) eleType).isCharType()) {
				result.append('\"');
				for (Expression element : elements) {
					result.append(element.toString());
				}
				result.append('\"');
				return result.toString();
			}
		}
		result.append("{");
		first = true;
		if (elements != null) {
			for (Expression element : elements) {
				if (first) {
					result.append(element.toString());
					first = false;
				} else {
					result.append(", ");
					result.append(element.toString());
				}
			}
		}
		result.append("}");
		return result.toString();
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
