package edu.udel.cis.vsl.civl.model.IF.type;

import java.util.Collection;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

//TODO: Document!!!

public interface CIVLBundleType extends CIVLType {

	int getNumTypes();

	SymbolicType getElementType(int index);

	//TODO: What does this do if the type isn't found?
	Integer getIndexOf(SymbolicType elementType);

	boolean isComplete();

	void complete(Collection<SymbolicType> elementTypes,
			SymbolicUnionType dynamicType);

	@Override
	SymbolicUnionType getDynamicType(SymbolicUniverse universe);

}
