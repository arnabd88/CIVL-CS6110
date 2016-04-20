/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
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
	public CommonSystemFunction(CIVLSource source, Identifier name,
			List<Variable> parameters, CIVLType returnType,
			Scope containingScope, Location startLocation,
			ModelFactory factory, String libraryName) {
		super(source, name, parameters, returnType, containingScope,
				startLocation, factory);
		this.isSystem = true;
		this.library = libraryName;
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
	
	@Override
	public boolean isLibraryFunction(){
		return true;
	}

	@Override
	public boolean isNormal() {
		return false;
	}
}
