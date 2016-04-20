package edu.udel.cis.vsl.civl.model.common.type;

import java.util.LinkedList;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLFunctionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * A function type has the declaration of the following format: int (int,int).
 * 
 * @author Manchun Zheng
 * 
 */
public class CommonFunctionType extends CommonType implements CIVLFunctionType {

	/* ************************** Instance Fields ************************** */

	/**
	 * The return type of this function type.
	 */
	private CIVLType returnType;

	/**
	 * The types of the parameter list of this function type.
	 */
	private CIVLType[] parameterTypes;

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of function type.
	 * 
	 * @param returnType
	 *            The return type of the function type.
	 * @param parasTypes
	 *            The types of the parameter list.
	 */
	public CommonFunctionType(CIVLType returnType, CIVLType[] parasTypes) {
		this.returnType = returnType;
		this.parameterTypes = parasTypes;
	}

	/* ******************* Methods from CIVLFunctionType ******************* */

	@Override
	public boolean hasState() {
		if (this.returnType.hasState())
			return true;
		for (CIVLType parameterType : this.parameterTypes) {
			if (parameterType.hasState())
				return true;
		}
		return false;
	}

	@Override
	public SymbolicType getDynamicType(SymbolicUniverse universe) {
		if (dynamicType != null)
			return dynamicType;
		else {
			LinkedList<SymbolicType> parameterDynamicTypes = new LinkedList<>();

			parameterDynamicTypes.add(returnType.getDynamicType(universe));
			for (CIVLType parameterType : this.parameterTypes) {
				parameterDynamicTypes.add(parameterType
						.getDynamicType(universe));
			}
			return this.dynamicType;
		}
	}

	@Override
	public CIVLType returnType() {
		return this.returnType;
	}

	@Override
	public CIVLType[] parameterTypes() {
		return this.parameterTypes;
	}

	@Override
	public String toString() {
		String result = returnType.toString() + " (";

		if (this.parameterTypes != null) {
			for (CIVLType type : parameterTypes) {
				result += type.toString() + ", ";
			}
		}
		result = result.substring(0, result.length() - 2);
		result += ")";
		result = "(" + result + ")";
		return result;
	}

	@Override
	public void setReturnType(CIVLType type) {
		this.returnType = type;
	}

	@Override
	public void setParameterTypes(CIVLType[] types) {
		this.parameterTypes = types;
	}

	@Override
	public TypeKind typeKind() {
		return TypeKind.FUNCTION;
	}

}
