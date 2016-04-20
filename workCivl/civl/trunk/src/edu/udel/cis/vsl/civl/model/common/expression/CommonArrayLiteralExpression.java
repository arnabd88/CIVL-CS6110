package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.ArrayList;
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
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class CommonArrayLiteralExpression extends CommonExpression implements
		ArrayLiteralExpression {

	/* ************************** Private Fields *************************** */

	/**
	 * The elements of the array literal.
	 */
	private Expression[] elements;

	/* **************************** Constructor **************************** */

	/**
	 * Create a new instance of an array literal expression.
	 * 
	 * @param source
	 *            The source information corresponding to this array literal.
	 * @param scope
	 *            The highest scope that this array literal accessed through its
	 *            elements.
	 * @param arrayType
	 *            The type of this array literal.
	 * @param elements
	 *            The elements of this array literal.
	 */
	public CommonArrayLiteralExpression(CIVLSource source, Scope hscope,
			Scope lscope, CIVLArrayType arrayType, List<Expression> elements) {
		super(source, hscope, lscope, arrayType);
		this.elements = new Expression[elements.size()];
		elements.toArray(this.elements);
	}

	/* *************** Methods from ArrayLiteralExpression ***************** */

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

	/* ****************** Methods from LiteralExpression ******************* */

	@Override
	public LiteralKind literalKind() {
		return LiteralKind.ARRAY;
	}

	/* ********************* Methods from Expression *********************** */

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ARRAY_LITERAL;
	};

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

	/* ************************ Methods from Object ************************ */

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
	public void calculateConstantValueWork(SymbolicUniverse universe) {
		List<SymbolicExpression> elementValues = new ArrayList<>();
		SymbolicType elementType = this.elementType().getDynamicType(universe);

		for (Expression element : elements) {
			SymbolicExpression elementValue;

			element.calculateConstantValue(universe);
			elementValue = element.constantValue();
			if (elementValue == null)
				return;
			elementValues.add(elementValue);
			elementType = elementValue.type();
		}
		this.constantValue = universe.array(elementType, elementValues);
	}

	@Override
	public void setLiteralConstantValue(SymbolicExpression value) {
		this.constantValue = value;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		ArrayLiteralExpression that = (ArrayLiteralExpression) expression;
		int thisElementsLength = this.elements.length;

		if (thisElementsLength == that.elements().length) {
			for (int i = 0; i < thisElementsLength; i++)
				if (!this.elements[i].equals(that.elements()[i]))
					return false;
			return true;
		}
		return false;
	}

	@Override
	public boolean containsHere() {
		for (Expression ele : elements) {
			if (ele.containsHere())
				return true;
		}
		return false;
	}
}
