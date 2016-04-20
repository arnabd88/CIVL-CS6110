package edu.udel.cis.vsl.sarl.expr.cnf;

import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

// interface BooleanExpression extends SymbolicExpression

// every BooleanExpression is either a BooleanPrimitive or a
// CompoundBooleanExpression

// class CompoundBooleanExpression extends Homogeneous<BooleanExpression>
// extends
// BooleanExpression. Used for AND and OR and NOT.

// class: BooleanPrimitive extends Homogeneous<SymbolicObject>:
// used for any BooleanExpression that is not an AND or OR or NOT
// true = Concrete(true), false =Concrete(false)

public class CompoundBooleanExpression extends
		HomogeneousExpression<BooleanExpression> implements BooleanExpression {

	/**
	 * The negation of this boolean expression. Cached here for performance.
	 */
	private BooleanExpression negation = null;

	/**
	 * Is this boolean expression "valid", i.e., equivalent to true, i.e., a
	 * tautology? Result is cached here for convenience. There are four possible
	 * values: (1) null: nothing is known and nothing has been tried to figure
	 * it out, (2) YES: it is definitely valid, (3) NO: it is definitely not
	 * valid, and (4) MAYBE: unknown. The difference between null and MAYBE is
	 * that with MAYBE you know we already tried to figure out if it is valid
	 * and couldn't, hence, there is no need to try again.
	 */
	private ResultType validity = null;

	public CompoundBooleanExpression(SymbolicOperator operator,
			SymbolicType type, BooleanExpression... args) {
		super(operator, type, args);
		assert operator == SymbolicOperator.AND
				|| operator == SymbolicOperator.OR
				|| operator == SymbolicOperator.NOT;
	}

	protected BooleanExpression getNegation() {
		return negation;
	}

	protected void setNegation(BooleanExpression value) {
		this.negation = value;
	}

	@Override
	public ResultType getValidity() {
		return validity;
	}

	@Override
	public void setValidity(ResultType value) {
		this.validity = value;
	}

	@Override
	public void canonizeChildren(ObjectFactory factory) {
		super.canonizeChildren(factory);

		if (negation != null)
			negation = factory.canonic(negation);
	}

	@Override
	public BooleanExpression[] getClauses() {
		if (operator == SymbolicOperator.AND)
			return arguments;
		return new BooleanExpression[] { this };
	}

}
