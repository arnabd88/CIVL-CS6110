package edu.udel.cis.vsl.civl.semantics;

import java.util.List;
import java.util.Vector;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.Initializer;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class CommonInitializer implements Initializer {

	private SymbolicUniverse symbolicUniverse;

	private SymbolicType processType;

	/**
	 * Get the symbolic type of an array.
	 * 
	 * @param type
	 *            The model array type.
	 * @return The symbolic array type.
	 */
	private SymbolicType arrayType(CIVLSource source, CIVLArrayType type) {
		CIVLType baseType = type.elementType();

		if (baseType instanceof CIVLArrayType) {
			return symbolicUniverse.arrayType(arrayType(source,
					(CIVLArrayType) baseType));
		} else if (baseType instanceof CIVLPrimitiveType) {
			switch (((CIVLPrimitiveType) baseType).primitiveTypeKind()) {
			case INT:
				return symbolicUniverse.arrayType(symbolicUniverse
						.integerType());
			case BOOL:
				return symbolicUniverse.arrayType(symbolicUniverse
						.booleanType());
			case REAL:
				return symbolicUniverse.arrayType(symbolicUniverse.realType());
			case STRING:
				return symbolicUniverse.arrayType(symbolicUniverse
						.characterType());
			default:
				break;
			}
		} else if (baseType.isProcessType()) {
			return symbolicUniverse.arrayType(processType);
		} else if (baseType instanceof CIVLStructType) {
			return structType(source, (CIVLStructType) baseType);
		}
		throw new CIVLInternalException("Unknown type: " + baseType, source);
	}

	/**
	 * Get the symbolic type of a struct.
	 * 
	 * @param type
	 *            The model struct type.
	 * @return The symbolic struct type, which is a tuple whose component types
	 *         are the symbolic types corresponding to the struct's fields.
	 */
	private SymbolicType structType(CIVLSource source, CIVLStructType type) {
		SymbolicType result;
		StringObject name = symbolicUniverse.stringObject(type.name().name());
		List<SymbolicType> fieldTypes = new Vector<SymbolicType>();

		for (StructField f : type.fields()) {
			SymbolicType fieldType = null;

			if (f.type() instanceof CIVLArrayType) {
				fieldType = arrayType(source, (CIVLArrayType) f.type());
			} else if (f.type() instanceof CIVLPrimitiveType) {
				switch (((CIVLPrimitiveType) f.type()).primitiveTypeKind()) {
				case INT:
					fieldType = symbolicUniverse.integerType();
					break;
				case BOOL:
					fieldType = symbolicUniverse.booleanType();
					break;
				case REAL:
					fieldType = symbolicUniverse.realType();
					break;
				case STRING:
					// TODO: Handle this.
				default:
					break;
				}
			} else if (f.type().isProcessType()) {
				fieldType = symbolicUniverse.arrayType(processType);
			} else if (f.type() instanceof CIVLStructType) {
				// TODO: Handle recursive types.
				fieldType = structType(source, (CIVLStructType) f.type());
			} else if (f.type() instanceof CIVLPointerType) {
				List<SymbolicType> pointerComponents = new Vector<SymbolicType>();

				pointerComponents.add(symbolicUniverse.integerType());
				pointerComponents.add(symbolicUniverse.integerType());
				pointerComponents.add(symbolicUniverse
						.arrayType(symbolicUniverse.integerType()));
				fieldType = symbolicUniverse.tupleType(
						symbolicUniverse.stringObject("pointer"),
						pointerComponents);
			}
			fieldTypes.add(fieldType);
		}
		result = symbolicUniverse.tupleType(name, fieldTypes);
		return result;
	}

	/**
	 * For now: default is null. This is bad. Use universe.nullExpression()
	 * instead.
	 * 
	 * Exceptions: arrays, structs, and input variables.
	 */
	@Override
	public SymbolicExpression initialValue(State state, Variable v,
			int dynamicScopeId) {
		int i = v.vid();

		if (v.type() instanceof CIVLArrayType) {
			StringObject name = symbolicUniverse.stringObject("A_s"
					+ dynamicScopeId + "v" + i);
			SymbolicType type = arrayType(v.getSource(),
					(CIVLArrayType) v.type());

			return symbolicUniverse.symbolicConstant(name, type);
		} else if (v.type() instanceof CIVLStructType) {
			StringObject name = symbolicUniverse.stringObject("S_s"
					+ dynamicScopeId + "v" + i);
			SymbolicType type = structType(v.getSource(),
					(CIVLStructType) v.type());

			return symbolicUniverse.symbolicConstant(name, type);
		} else if (v.isInput()) {
			StringObject name = symbolicUniverse.stringObject("s"
					+ dynamicScopeId + "v" + i);
			SymbolicType type = null;

			if (v.type() instanceof CIVLPrimitiveType) {
				switch (((CIVLPrimitiveType) v.type()).primitiveTypeKind()) {
				case INT:
					type = symbolicUniverse.integerType();
					break;
				case BOOL:
					type = symbolicUniverse.booleanType();
					break;
				case REAL:
					type = symbolicUniverse.realType();
					break;
				case STRING:
					type = symbolicUniverse.arrayType(symbolicUniverse
							.characterType());
					break;
				default:
					throw new CIVLInternalException("Unreachable",
							v.getSource());
				}
			} else {
				throw new CIVLInternalException("Unimplemented input type: "
						+ v.type(), v.getSource());
			}
			return symbolicUniverse.symbolicConstant(name, type);
		}
		return null;
	}

}
