package edu.udel.cis.vsl.abc.front.c.parse;

import java.util.Set;

/**
 * This contains the information of symbols defined in a scope or the ancestors
 * of that scope, including the set of types and enumeration constants
 * 
 * @author Manchun Zheng
 * 
 */
public class ScopeSymbols {

	public Set<String> types;
	public Set<String> enumerationConstants;

	// boolean isFunctionDefinition;

	public ScopeSymbols(Set<String> types, Set<String> enumConsts) {
		this.types = types;
		this.enumerationConstants = enumConsts;
	}
}
