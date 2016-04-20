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
package edu.udel.cis.vsl.sarl.ideal.IF;

/**
 * A Monic is a product of powers of primitive expressions x<sub>1</sub><sup>i
 * <sub>1</sub></sup>*...*x<sub>n</sub><sup>i<sub>n</sub></sup>, where the x
 * <sub>i</sub> are primitives and the i<sub>j</sub> are positive concrete ints.
 * 
 * @author siegel
 */
public interface Monic extends Monomial {

	/**
	 * Returns the factors of this monic as a map from {@link Primitive} to
	 * {@link PrimitivePower}. A key in the map is a primitive x and the value
	 * associated to x will be a primitive power x<sup>i</sup> (x raised to the
	 * i<sup>th</sup> power) for some positive integer i.
	 * 
	 * @param factory
	 *            the factory used to produce this monic
	 * 
	 * @return the factors of this monic as a map
	 */
	PrimitivePower[] monicFactors(IdealFactory factory);

	/**
	 * Is this the trivial monic, i.e., the monic consisting of 0 factors (and
	 * therefore equivalent to 1)?
	 * 
	 * @return <code>true</code> iff this monic is trivial
	 */
	boolean isTrivialMonic();

	@Override
	Monic powerInt(IdealFactory factory, int exponent);
}
