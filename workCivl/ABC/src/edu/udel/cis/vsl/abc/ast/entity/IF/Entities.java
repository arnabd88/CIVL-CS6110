package edu.udel.cis.vsl.abc.ast.entity.IF;

import edu.udel.cis.vsl.abc.ast.entity.common.CommonEntityFactory;

/**
 * Factory class providing a static method to get a new {@link EntityFactory}.
 * This is the entry point for module <strong>ast.entity</strong>.
 * 
 * @author siegel
 * 
 */
public class Entities {

	/**
	 * Constructs a new entity factory.
	 * 
	 * @return the new entity factory
	 */
	public static EntityFactory newEntityFactory() {
		return new CommonEntityFactory();
	}

}
