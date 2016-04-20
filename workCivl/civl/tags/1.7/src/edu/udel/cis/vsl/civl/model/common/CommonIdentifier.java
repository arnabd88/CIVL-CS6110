/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;

/**
 * An identifier. Used for names of variables, functions, etc.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonIdentifier extends CommonSourceable implements Identifier {

	private StringObject stringObject;

	/**
	 * An identifier. Used for names of variables, functions, etc.
	 * 
	 * @param name
	 *            The name associated with this identifier.
	 */
	public CommonIdentifier(CIVLSource source, StringObject stringObject) {
		super(source);
		this.stringObject = stringObject;
	}

	/**
	 * @return The name associated with this identifier.
	 */
	public String name() {
		return stringObject.getString();
	}
	
	@Override
	public String toString() {
		return stringObject.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((stringObject == null) ? 0 : stringObject.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Identifier other = (Identifier) obj;
		if (stringObject == null) {
			if (other.stringObject() != null)
				return false;
		} else if (!stringObject.equals(other.stringObject()))
			return false;
		return true;
	}

	@Override
	public StringObject stringObject() {
		return stringObject;
	}

}
