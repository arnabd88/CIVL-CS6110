package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;

public class Transforms {

	public static TransformerFactory newTransformerFactory(ASTFactory astFactory) {
		return new TransformerFactory(astFactory);
	}

}
