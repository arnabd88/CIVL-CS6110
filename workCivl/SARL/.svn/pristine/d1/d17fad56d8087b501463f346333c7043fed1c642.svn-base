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
package edu.udel.cis.vsl.sarl.type.common;

import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * Implementation of {@link SymbolicUnionType}.
 */
public class CommonSymbolicUnionType extends CommonSymbolicType
		implements SymbolicUnionType {

	private final static int classCode = CommonSymbolicUnionType.class
			.hashCode();
	/**
	 * sequence used to create the unionType
	 */
	private SymbolicTypeSequence sequence;

	/**
	 * holds the name of this unionType
	 */
	private StringObject name;

	/**
	 * holds the pureType of this unionType
	 */
	private SymbolicUnionType pureType;

	/**
	 * The elements of the sequence must be unique, i.e., no repetitions.
	 * 
	 * @param name
	 * @param sequence
	 */
	CommonSymbolicUnionType(StringObject name, SymbolicTypeSequence sequence) {
		super(SymbolicTypeKind.UNION);
		assert sequence != null;
		assert name != null;
		this.name = name;
		this.sequence = sequence;
	}

	@Override
	protected boolean typeEquals(CommonSymbolicType thatType) {
		CommonSymbolicUnionType that = (CommonSymbolicUnionType) thatType;

		return name.equals(that.name) && sequence.equals(that.sequence);
	}

	@Override
	protected int computeHashCode() {
		return classCode ^ name.hashCode() ^ sequence.hashCode();
	}

	@Override
	public StringBuffer toStringBuffer(boolean atomize) {
		StringBuffer result = new StringBuffer("Union[");

		result.append(name.toStringBuffer(false));
		result.append(",");
		result.append(sequence.toStringBuffer(false));
		result.append("]");
		return result;
	}

	@Override
	public StringObject name() {
		return name;
	}

	@Override
	public SymbolicTypeSequence sequence() {
		return sequence;
	}

	@Override
	public void canonizeChildren(ObjectFactory factory) {
		if (!sequence.isCanonic())
			sequence = (CommonSymbolicTypeSequence) factory.canonic(sequence);
		if (!name.isCanonic())
			name = (StringObject) factory.canonic(name);
		if (pureType != null && !pureType.isCanonic())
			pureType = factory.canonic(pureType);
	}

	/**
	 * @return the pureType of this unionType You have to set the pureType first
	 *         using setPureType(...)
	 */
	public SymbolicUnionType getPureType() {
		return pureType;
	}

	/**
	 * used to set the pureType of this unionType
	 * 
	 * @param pureType
	 */
	public void setPureType(SymbolicUnionType pureType) {
		this.pureType = pureType;
	}
}
