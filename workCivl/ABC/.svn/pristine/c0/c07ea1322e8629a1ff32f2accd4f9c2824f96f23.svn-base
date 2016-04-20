package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.CharacterConstantNode;
import edu.udel.cis.vsl.abc.ast.value.IF.CharacterValue;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonCharacterConstantNode extends CommonConstantNode implements
		CharacterConstantNode {

	public CommonCharacterConstantNode(Source source, String representation,
			CharacterValue value) {
		super(source, representation, value.getType());
		setConstantValue(value);
	}

	@Override
	public String toString() {
		return "CharacterConstantNode[" + getConstantValue() + "]";
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print(this);
	}

	@Override
	public CharacterValue getConstantValue() {
		return (CharacterValue) super.getConstantValue();
	}

	@Override
	public CharacterConstantNode copy() {
		return new CommonCharacterConstantNode(getSource(),
				getStringRepresentation(), getConstantValue());
	}

	@Override
	public ConstantKind constantKind() {
		return ConstantKind.CHAR;
	}

}
