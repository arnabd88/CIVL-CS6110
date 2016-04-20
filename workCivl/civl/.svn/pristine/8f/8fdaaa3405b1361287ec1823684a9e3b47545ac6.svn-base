/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.type;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.civl.model.IF.type.StructType;

/**
 * @author zirkel
 * 
 */
public class CommonStructType implements StructType {

	private List<StructField> fields;

	/**
	 * A struct type has a sequence of struct fields.
	 * 
	 * @param fields
	 *            A list of struct fields.
	 * 
	 */
	public CommonStructType(List<StructField> fields) {
		this.fields = fields;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.type.StructType#fields()
	 */
	@Override
	public List<StructField> fields() {
		return fields;
	}

}
