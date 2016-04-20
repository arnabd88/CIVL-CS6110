package edu.udel.cis.vsl.civl.model.common.type;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLRegularRangeType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.common.CommonIdentifier;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;

public class CommonRegularRangeType extends CommonStructOrUnionType implements
		CIVLRegularRangeType {

	public CommonRegularRangeType(Identifier name, SymbolicUniverse universe,
			CIVLType integerType) {
		super(name, true);
		List<StructOrUnionField> myfields = new ArrayList<>(3);

		myfields.add(new CommonStructOrUnionField(new CommonIdentifier(name
				.getSource(), (StringObject) universe.canonic(universe
				.stringObject("low"))), integerType));
		myfields.add(new CommonStructOrUnionField(new CommonIdentifier(name
				.getSource(), (StringObject) universe.canonic(universe
				.stringObject("high"))), integerType));
		myfields.add(new CommonStructOrUnionField(new CommonIdentifier(name
				.getSource(), (StringObject) universe.canonic(universe
				.stringObject("step"))), integerType));
		this.complete(myfields);
	}
}
