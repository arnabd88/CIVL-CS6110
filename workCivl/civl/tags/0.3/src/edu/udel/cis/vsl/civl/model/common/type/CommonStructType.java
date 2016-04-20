/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.type;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructType;
import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * @author zirkel
 * 
 */
public class CommonStructType extends CommonType implements CIVLStructType {

	private Identifier name;

	private StructField[] fields = null;

	public CommonStructType(Identifier name) {
		this.name = name;
	}

	@Override
	public Iterable<StructField> fields() {
		return Arrays.asList(fields);
	}

	@Override
	public Identifier name() {
		return name;
	}

	
	
	@Override
	public String toString() {
		String result = "struct " + name.toString();

		// if (isComplete()) {
		// result += "{";
		// boolean first = true;
		//
		// for (StructField f : fields) {
		// if (first)
		// first = false;
		// else
		// result += ", ";
		// if (f.type() instanceof CIVLStructType)
		// result += ((CIVLStructType) f.type()).name();
		// else
		// result += f.toString();
		// }
		// result += "}";
		// }
		return result;
	}

	@Override
	public int numFields() {
		return fields.length;
	}

	@Override
	public StructField getField(int index) {
		return fields[index];
	}

	@Override
	public boolean hasState() {
		if (!isComplete())
			throw new CIVLInternalException("Struct not complete",
					(CIVLSource) null);
		for (StructField field : fields) {
			if (field.type().hasState())
				return true;
		}
		return false;
	}

	@Override
	public boolean isComplete() {
		return fields != null;
	}

	@Override
	public void complete(Collection<StructField> fields) {
		if (isComplete())
			throw new CIVLInternalException("Struct already complete",
					(CIVLSource) null);
		else {
			int numFields = fields.size();
			int count = 0;

			this.fields = new StructField[numFields];
			for (StructField field : fields) {
				this.fields[count] = field;
				count++;
			}
		}
	}

	@Override
	public void complete(StructField[] fields) {
		if (isComplete())
			throw new CIVLInternalException("Struct already complete",
					(CIVLSource) null);
		else {
			int numFields = fields.length;
			int count = 0;

			this.fields = new StructField[numFields];
			for (StructField field : fields) {
				this.fields[count] = field;
				count++;
			}
		}
	}

	@Override
	public SymbolicType getDynamicType(SymbolicUniverse universe) {
		if (dynamicType == null) {
			if (!isComplete())
				throw new CIVLInternalException(
						"cannot get dynamic type of incomplete struct type: "
								+ this, (CIVLSource) null);
			else {
				LinkedList<SymbolicType> fieldDynamicTypes = new LinkedList<SymbolicType>();

				for (StructField field : fields) {
					SymbolicType fieldDynamicType = field.type()
							.getDynamicType(universe);

					fieldDynamicTypes.add(fieldDynamicType);
				}
				dynamicType = universe.tupleType(
						universe.stringObject(name.name()), fieldDynamicTypes);
				dynamicType = (SymbolicType) universe.canonic(dynamicType);
			}
		}
		return dynamicType;
	}
	
	@Override
	public boolean isStructType() {
		return true;
	}

}
