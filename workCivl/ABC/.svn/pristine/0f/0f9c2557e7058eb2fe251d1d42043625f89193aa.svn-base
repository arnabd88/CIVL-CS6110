package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;
import java.util.Arrays;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.QuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

/**
 * A quantified expression consists of a quantifier, a variable bound by the
 * quantifier, an expression restricting the values of the quantified variable,
 * and a quantified expression. e.g. forall {int x | x > 1} x > 0;
 * 
 * @author zirkel
 * 
 */
public class CommonQuantifiedExpressionNode extends CommonExpressionNode
		implements QuantifiedExpressionNode {

	private Quantifier quantifier;
	// private VariableDeclarationNode variable;
	// private ExpressionNode restriction;
	private boolean isRange;

	// private ExpressionNode lower;
	// private ExpressionNode upper;
	// private ExpressionNode expression;

	/**
	 * @param source
	 *            The source code information for this expression.
	 * @param quantifier
	 *            The quantifier for this expression. One of {FORALL, EXISTS,
	 *            UNIFORM}.
	 * @param variable
	 *            The quantified variable.
	 * @param restriction
	 *            Boolean-valued expression
	 */
	public CommonQuantifiedExpressionNode(Source source, Quantifier quantifier,
			VariableDeclarationNode variable, ExpressionNode restriction,
			ExpressionNode expression) {
		super(source, Arrays.asList(variable, restriction, expression, null,
				null));
		this.quantifier = quantifier;
		// this.variable = variable;
		// this.restriction = restriction;
		// this.expression = expression;
		// this.lower = null;
		// this.upper = null;
		isRange = false;
	}

	/**
	 * @param source
	 *            The source code information for this expression.
	 * @param quantifier
	 *            The quantifier for this expression. One of {FORALL, EXISTS,
	 *            UNIFORM}.
	 * @param variable
	 *            The quantified variable.
	 * @param lower
	 *            Integer-valued expression for the lower bound on the
	 *            quantified variable.
	 * @param upper
	 *            Integer-valued expression for the upper bound on the
	 *            quantified variable.
	 */
	public CommonQuantifiedExpressionNode(Source source, Quantifier quantifier,
			VariableDeclarationNode variable, ExpressionNode lower,
			ExpressionNode upper, ExpressionNode expression) {
		// super(source, variable, upper, expression);
		super(source, Arrays.asList(variable, null, expression, lower, upper));
		this.quantifier = quantifier;
		// this.variable = variable;
		// this.lower = lower;
		// this.upper = upper;
		// this.expression = expression;
		// this.restriction = null;
		isRange = true;
	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	@Override
	public ExpressionNode copy() {
		if (isRange()) {
			return new CommonQuantifiedExpressionNode(this.getSource(),
					quantifier, variable().copy(), lower().copy(), upper()
							.copy(), expression().copy());
		}
		return new CommonQuantifiedExpressionNode(this.getSource(), quantifier,
				variable().copy(), restriction().copy(), expression().copy());
	}

	@Override
	public Quantifier quantifier() {
		return quantifier;
	}

	@Override
	public VariableDeclarationNode variable() {
		return (VariableDeclarationNode) this.child(0);
	}

	@Override
	public ExpressionNode restriction() {
		return (ExpressionNode) this.child(1);
	}

	@Override
	public ExpressionNode expression() {
		return (ExpressionNode) this.child(2);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode#printBody(java.io.
	 * PrintStream)
	 */
	@Override
	protected void printBody(PrintStream out) {
		String output = "";

		switch (quantifier) {
		case FORALL:
			output = "forall";
			break;
		case EXISTS:
			output = "exists";
			break;
		case UNIFORM:
			output = "uniform";
			break;
		}
		out.print(output);
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.QUANTIFIED_EXPRESSION;
	}

	@Override
	public boolean isRange() {
		return isRange;
	}

	@Override
	public ExpressionNode lower() {
		return (ExpressionNode) this.child(3);
	}

	@Override
	public ExpressionNode upper() {
		return (ExpressionNode) this.child(4);
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		boolean result = expression().isSideEffectFree(errorsAreSideEffects);

		if (this.restriction() == null) {
			result = result
					&& this.lower().isSideEffectFree(errorsAreSideEffects)
					&& this.upper().isSideEffectFree(errorsAreSideEffects);
		} else {
			result = result
					&& this.restriction()
							.isSideEffectFree(errorsAreSideEffects);
		}
		return result;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof QuantifiedExpressionNode) {
			QuantifiedExpressionNode thatQuan = (QuantifiedExpressionNode) that;

			if (this.isRange == thatQuan.isRange()
					&& this.quantifier == thatQuan.quantifier())
				return null;
			else
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different quantifier");
		}
		return new DifferenceObject(this, that);
	}
}
