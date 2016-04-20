package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.FloatingConstantNode;
import edu.udel.cis.vsl.abc.ast.value.IF.RealFloatingValue;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonFloatingConstantNode extends CommonConstantNode implements
		FloatingConstantNode {

	private String wholePart;

	private String fractionPart;

	private String exponent;

	public CommonFloatingConstantNode(Source source, String representation,
			String wholePart, String fractionPart, String exponent,
			RealFloatingValue value) {
		super(source, representation, value.getType());
		this.wholePart = wholePart;
		this.fractionPart = fractionPart;
		this.exponent = exponent;
		setConstantValue(value);
	}

	@Override
	public RealFloatingValue getConstantValue() {
		return (RealFloatingValue) super.getConstantValue();
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print(toString());
	}

	@Override
	public String toString() {
		return "FloatingConstantNode[radix=" + getConstantValue().getRadix()
				+ ", significand=" + wholePart + "." + fractionPart
				+ ", exponent=" + exponent + ", doubleValue="
				+ getConstantValue().getDoubleValue() + "]";
	}

	@Override
	public String wholePart() {
		return wholePart;
	}

	@Override
	public String fractionPart() {
		return fractionPart;
	}

	@Override
	public String exponent() {
		return exponent;
	}

	@Override
	public FloatingConstantNode copy() {
		return new CommonFloatingConstantNode(getSource(),
				getStringRepresentation(), wholePart(), fractionPart(),
				exponent(), getConstantValue());
	}

	@Override
	public ConstantKind constantKind() {
		return ConstantKind.FLOAT;
	}
}
