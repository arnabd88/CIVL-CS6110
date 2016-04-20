/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.expr.cnf;

import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * A representation of a {@link BooleanExpression} using Conjunctive Normal
 * Form.
 * 
 * @author siegel
 */
public class BooleanPrimitive extends HomogeneousExpression<SymbolicObject>
		implements BooleanExpression {

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

	/**
	 * One of several constructors that build a CnfExpression.
	 * 
	 * @param kind
	 * @param type
	 * @param args
	 *            args is an array of Symbolic Objects
	 */
	protected BooleanPrimitive(SymbolicOperator kind, SymbolicType type,
			SymbolicObject... args) {
		super(kind, type, args);
		assert type.isBoolean();
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

	public BooleanExpression[] getClauses() {
		return new BooleanExpression[] { this };
	}

}
