/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import edu.udel.cis.vsl.civl.model.IF.Identifier;

/**
 * An identifier.  Used for names of variables, functions, etc.
 * 
 * @author Timothy K. Zirkel (zirkel)
 *
 */
public class CommonIdentifier implements Identifier {

	private String name;
	
	/**
	 * An identifier.  Used for names of variables, functions, etc.
	 * 
	 * @param name The name associated with this identifier.
	 */
	public CommonIdentifier(String name) {
		this.name = name;
	}

	/**
	 * @return The name associated with this identifier.
	 */
	public String name() {
		return name;
	}
	
	/**
	 * @param name The name associated with this identifier.
	 */
	public void setName(String name) {
		this.name = name;
	}
	
	@Override
	public String toString() {
		return name;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		return result;
	}

	/* (non-Javadoc)
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
		if (name == null) {
			if (other.name() != null)
				return false;
		} else if (!name.equals(other.name()))
			return false;
		return true;
	}
	
	
	
}
