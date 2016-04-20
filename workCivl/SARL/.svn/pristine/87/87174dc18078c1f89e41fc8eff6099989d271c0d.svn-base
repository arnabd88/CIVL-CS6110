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

import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.util.BinaryOperator;

/**
 * Divides: <i>p<sup>i</sup></i> / <i>p<sup>j</sup></i>, where <i>p</i> is a
 * {@link Primitive} and <i>i</i> and <i>j</i> are positive {@link IntObject}s
 * with <i>i</i> &ge; <i>j</i>. The answer is <i>p<sup>i-j</sup></i> if <i>i</i>
 * &gt; <i>j</i>, or <code>null</code> if <i>i</i> = <i>j</i>.
 * 
 * @author siegel
 * 
 */
class PrimitivePowerDivider implements BinaryOperator<PrimitivePower> {

	private IdealFactory idealFactory;

	private ObjectFactory objectFactory;

	public PrimitivePowerDivider(IdealFactory idealFactory) {
		this.idealFactory = idealFactory;
		this.objectFactory = idealFactory.objectFactory();
	}

	@Override
	public PrimitivePower apply(PrimitivePower arg0, PrimitivePower arg1) {
		int exp0 = arg0.primitivePowerExponent(idealFactory).getInt(),
				exp1 = arg1.primitivePowerExponent(idealFactory).getInt();
		int difference = exp0 - exp1;

		if (difference == 0)
			return null;
		else
			return idealFactory.primitivePower(arg0.primitive(idealFactory),
					objectFactory.intObject(difference));

	}
}
