package edu.udel.cis.vsl.abc.ast.value.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.ast.value.common.CommonValueFactory;
import edu.udel.cis.vsl.abc.config.IF.Configuration;

public class Values {

	public static ValueFactory newValueFactory(Configuration configuration,
			TypeFactory typeFactory) {
		return new CommonValueFactory(configuration, typeFactory);
	}

}
