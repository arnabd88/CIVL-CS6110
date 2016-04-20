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

import edu.udel.cis.vsl.sarl.IF.object.IntObject;

/**
 * A power of a {@link Primitive} expression, x<sup>i</sup>, where x is a
 * {@link Primitive} and i is a concrete positive int.
 * 
 * @author siegel
 */
public interface PrimitivePower extends Monic {

	/**
	 * Returns the {@link Primitive} which is the base in this primitive power
	 * expression.
	 * 
	 * @param factory
	 *            the ideal factory owning this expression
	 * 
	 * @return the base in this primitive power expansion
	 */
	Primitive primitive(IdealFactory factory);

	/**
	 * Returns the exponent in this primitive power expression, which is a
	 * positive integer represented as an {@link IntObject}.
	 * 
	 * @param factory
	 *            the ideal factory owning this expression
	 * 
	 * @return the exponent of this expression
	 */
	IntObject primitivePowerExponent(IdealFactory factory);

	@Override
	PrimitivePower powerInt(IdealFactory factory, int exponent);

}
