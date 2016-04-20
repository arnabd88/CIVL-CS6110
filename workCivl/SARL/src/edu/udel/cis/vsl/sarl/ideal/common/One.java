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
package edu.udel.cis.vsl.sarl.ideal.common;

import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * Empty monic: equivalent to 1. The number 1 is the only thing which is both a
 * {@link Monic} and a {@link Constant}. Can have either integer of real type.
 * 
 * @author siegel
 */
public class One extends HomogeneousExpression<SymbolicObject>
		implements Constant, Monic {

	private final static PrimitivePower[] emptyFactorList = new PrimitivePower[0];

	/**
	 * Cache of value returned by {@link #termMap(IdealFactory)}.
	 */
	private Monomial[] termMap = null;

	/**
	 * Constructs new instance of {@link One} of given type. The number object
	 * <code>oneObj</code> must be either the real or integer number 1. The
	 * <code>type</code> must be consistent with the type of <code>oneObj</code>
	 * .
	 * 
	 * @param type
	 *            either a {@link SymbolicIntegerType} or
	 *            {@link SymbolicRealType};
	 * 
	 * @param oneObj
	 *            either the integer 1 or the real number 1
	 */
	protected One(SymbolicType type, NumberObject oneObj) {
		super(SymbolicOperator.CONCRETE, type, new SymbolicObject[] { oneObj });
		assert oneObj.isOne();
	}

	@Override
	public Constant monomialConstant(IdealFactory factory) {
		return this;
	}

	@Override
	public Monic monic(IdealFactory factory) {
		return this;
	}

	@Override
	public Monomial numerator(IdealFactory factory) {
		return this;
	}

	@Override
	public Monomial denominator(IdealFactory factory) {
		return this;
	}

	@Override
	public PrimitivePower[] monicFactors(IdealFactory factory) {
		return emptyFactorList;
	}

	@Override
	public boolean isTrivialMonic() {
		return true;
	}

	@Override
	public Monomial[] termMap(IdealFactory factory) {
		if (termMap == null) {
			termMap = new Monomial[] { this };
			if (isCanonic())
				factory.objectFactory().canonize(termMap);
		}
		return termMap;
	}

	@Override
	public boolean isOne() {
		return true;
	}

	@Override
	public String toString() {
		return "1";
	}

	@Override
	public NumberObject value() {
		return (NumberObject) argument(0);
	}

	@Override
	public Number number() {
		return value().getNumber();
	}

	@Override
	public int monomialDegree() {
		return 0;
	}

	@Override
	public Monomial[] expand(IdealFactory factory) {
		return termMap(factory);
	}

	@Override
	public int totalDegree() {
		return 0;
	}

	@Override
	public boolean hasNontrivialExpansion(IdealFactory factory) {
		return false;
	}

	@Override
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (termMap != null)
			of.canonize(termMap);
	}

	@Override
	public int monomialOrder(IdealFactory factory) {
		return 0;
	}

	@Override
	public Monomial[] lower(IdealFactory factory) {
		return termMap(factory);
	}

	@Override
	public RationalExpression powerRational(IdealFactory factory,
			RationalExpression exponent) {
		return this;
	}

	@Override
	public One powerInt(IdealFactory factory, int exponent) {
		return this;
	}

}
