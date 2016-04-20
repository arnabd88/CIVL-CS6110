/**
 * 
 */
package edu.udel.cis.vsl.civl.model;

import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.model.common.CommonModelBuilder;

/**
 * @author Timothy K. Zirkel (zirkel)
 *
 */
public class Models {
	
	public static ModelBuilder newModelBuilder() {
		return new CommonModelBuilder();
	}

}
