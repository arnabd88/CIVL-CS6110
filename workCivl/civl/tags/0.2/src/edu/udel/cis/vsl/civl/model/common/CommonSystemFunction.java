/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * @author zirkel
 * 
 */
public class CommonSystemFunction extends CommonFunction implements
		SystemFunction {

	private String library = null;

	/**
	 * @param name
	 * @param parameters
	 * @param returnType
	 * @param containingScope
	 * @param startLocation
	 * @param factory
	 */
	public CommonSystemFunction(Identifier name, Vector<Variable> parameters,
			Type returnType, Scope containingScope, Location startLocation,
			ModelFactory factory) {
		super(name, parameters, returnType, containingScope, startLocation,
				factory);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.SystemFunction#getLibrary()
	 */
	@Override
	public String getLibrary() {
		return library;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.SystemFunction#setLibrary(java.lang.String
	 * )
	 */
	@Override
	public void setLibrary(String libraryName) {
		this.library = libraryName;
	}

	@Override
	public String toString() {
		return this.name().name() + " : system function call";
	}
	
}
