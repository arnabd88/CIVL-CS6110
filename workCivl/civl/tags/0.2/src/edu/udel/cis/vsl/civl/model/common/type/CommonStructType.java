/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.type;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.civl.model.IF.type.StructType;

/**
 * @author zirkel
 * 
 */
public class CommonStructType implements StructType {

	private Identifier name;
	private List<StructField> fields;

	/**
	 * A struct type has a sequence of struct fields.
	 * 
	 * @param fields
	 *            A list of struct fields.
	 * 
	 */
	public CommonStructType(Identifier name, List<StructField> fields) {
		this.name = name;
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

	@Override
	public Identifier name() {
		return name;
	}
	
	@Override
	public String toString() {
		String result = "struct " + name.toString() + " {\n";
		
		for (StructField f : fields) {
			result += "  " + f.toString() + "\n";
		}
		result += "}";
		return result;
	}

}
