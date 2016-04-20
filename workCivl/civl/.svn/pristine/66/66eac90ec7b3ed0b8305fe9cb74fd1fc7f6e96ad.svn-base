/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.type;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * @author zirkel
 * 
 */
public class CommonStructOrUnionType extends CommonType implements
		CIVLStructOrUnionType {

	private boolean isStruct;

	private boolean isHandleObject;

	private Identifier name;

	private StructOrUnionField[] fields = null;

	/**
	 * Create a new (incomplete) struct or union.
	 * 
	 * @param name
	 *            The name of this struct or union.
	 * @param isStruct
	 *            True if a struct, false if a union.
	 */
	public CommonStructOrUnionType(Identifier name, boolean isStruct) {
		this.name = name;
		this.isStruct = isStruct;
		this.isHandleObject = false;
	}

	@Override
	public Iterable<StructOrUnionField> fields() {
		return Arrays.asList(fields);
	}

	@Override
	public Identifier name() {
		return name;
	}

	@Override
	public String toString() {
		if (this.isStruct)
			return "struct " + name.toString();
		else
			return "union " + name.toString();
	}

	@Override
	public int numFields() {
		return fields.length;
	}

	@Override
	public StructOrUnionField getField(int index) {
		return fields[index];
	}

	@Override
	public boolean hasState() {
		if (!isComplete())
			throw new CIVLInternalException((isStruct ? "Struct" : "Union")
					+ " not complete", (CIVLSource) null);
		for (StructOrUnionField field : fields) {
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
	public void complete(Collection<StructOrUnionField> fields) {
		if (isComplete())
			throw new CIVLInternalException((isStruct ? "Struct" : "Union")
					+ " already complete", (CIVLSource) null);
		else {
			int numFields = fields.size();
			int count = 0;

			this.fields = new StructOrUnionField[numFields];
			for (StructOrUnionField field : fields) {
				this.fields[count] = field;
				count++;
			}
		}
	}

	@Override
	public void complete(StructOrUnionField[] fields) {
		if (isComplete())
			throw new CIVLInternalException((isStruct ? "Struct" : "Union")
					+ "  already complete", (CIVLSource) null);
		else {
			int numFields = fields.length;
			int count = 0;

			this.fields = new StructOrUnionField[numFields];
			for (StructOrUnionField field : fields) {
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
						"cannot get dynamic type of incomplete "
								+ (isStruct ? "struct" : "union") + " type: "
								+ this, (CIVLSource) null);
			else {
				LinkedList<SymbolicType> fieldDynamicTypes = new LinkedList<SymbolicType>();

				for (StructOrUnionField field : fields) {
					SymbolicType fieldDynamicType = field.type()
							.getDynamicType(universe);

					fieldDynamicTypes.add(fieldDynamicType);
				}
				if (this.isStruct) {
					dynamicType = universe.tupleType(
							universe.stringObject(name.name()),
							fieldDynamicTypes);
				} else {
					dynamicType = universe.unionType(
							universe.stringObject(name.name()),
							fieldDynamicTypes);
				}
				dynamicType = (SymbolicType) universe.canonic(dynamicType);
			}
		}
		return dynamicType;
	}

	@Override
	public boolean isStructType() {
		return isStruct;
	}

	@Override
	public boolean isUnionType() {
		return !isStruct;
	}

	@Override
	public boolean isHandleObjectType() {
		return this.isHandleObject;
	}

	@Override
	public void setHandleObjectType(boolean value) {
		this.isHandleObject = value;
	}

	@Override
	public int getFieldIndex(String field) {
		for (int i = 0; i < fields.length; i++) {
			String name = fields[i].name().name();

			if (name.equals(field))
				return i;
		}
		return -1;
	}

	@Override
	public TypeKind typeKind() {
		return TypeKind.STRUCT_OR_UNION;
	}
}
