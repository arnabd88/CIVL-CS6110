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
package edu.udel.cis.vsl.sarl.IF.type;

/**
 * A real number type. There are currently three different kinds of real types:
 * the Herbrand real type, the floating-point real types, and the ideal real
 * type.
 * 
 * @author siegel
 */
public interface SymbolicRealType extends SymbolicType {

	/**
	 * The different kinds of real types.
	 * 
	 * @author siegel
	 */
	public enum RealKind {
		HERBRAND, FLOAT, IDEAL
	};

	/**
	 * Returns the kind of real type this is.
	 * 
	 * @return the kind of real type this is
	 */
	RealKind realKind();

}
