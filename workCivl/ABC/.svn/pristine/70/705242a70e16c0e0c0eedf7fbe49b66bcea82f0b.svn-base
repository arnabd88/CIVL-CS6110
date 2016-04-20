package edu.udel.cis.vsl.abc.ast.value.common;

import java.util.Arrays;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.value.IF.OperatorValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public class CommonOperatorValue extends CommonValue implements OperatorValue {

	private final static int classCode = CommonOperatorValue.class.hashCode();

	private Operator operator;

	private Value[] arguments;

	public CommonOperatorValue(Type type, Operator operator, Value[] arguments) {
		super(type);
		assert operator != null;
		assert arguments != null;
		this.operator = operator;
		this.arguments = arguments;
	}

	@Override
	public Operator getOperator() {
		return operator;
	}

	@Override
	public int getNumberOfArguments() {
		return arguments.length;
	}

	@Override
	public Value getArgument(int index) {
		return arguments[index];
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonOperatorValue) {
			CommonOperatorValue that = (CommonOperatorValue) object;

			return getType().equals(that.getType())
					&& operator == that.operator
					&& Arrays.equals(arguments, that.arguments);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + operator.hashCode()
				+ Arrays.hashCode(arguments);
	}

	@Override
	public Answer isZero() {
		return Answer.MAYBE;
	}

	@Override
	public String toString() {
		return operator + "[" + arguments + "]";
	}

}
