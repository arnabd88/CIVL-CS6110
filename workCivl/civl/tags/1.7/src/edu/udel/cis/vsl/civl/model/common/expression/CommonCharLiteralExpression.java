package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.CharLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class CommonCharLiteralExpression extends CommonExpression implements
		CharLiteralExpression {

	private char value;

	/**
	 * Create a new char literal expression.
	 * 
	 * @param source
	 */
	public CommonCharLiteralExpression(CIVLSource source, CIVLType type,
			char value) {
		super(source, null, null, type);
		this.value = value;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.CHAR_LITERAL;
	}

	@Override
	public char value() {
		return this.value;
	}

	@Override
	public void setValue(char value) {
		this.value = value;
	}

	@Override
	public String toString() {
		switch (value) {
		case 0:
			return "''";
		case '\u000C':
			return "'\\f'";
		case '\u0007':
			return "'\\a'";
		case '\b':
			return "'\\b'";
		case '\n':
			return "'\\n'";
		case '\t':
			return "'\\t'";
		case '\r':
			return "'\\r'";
		case ' ':
			return "' '";
		}
		return "'" + Character.toString(value) + "'";
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return null;
	}

	@Override
	public LiteralKind literalKind() {
		return LiteralKind.CHAR;
	}

	@Override
	public void calculateConstantValueWork(SymbolicUniverse universe) {
		this.constantValue = universe.character(this.value);
	}

	@Override
	public void setLiteralConstantValue(SymbolicExpression value) {
		this.constantValue = value;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		CharLiteralExpression that = (CharLiteralExpression) expression;

		return this.value == that.value();
	}
}
