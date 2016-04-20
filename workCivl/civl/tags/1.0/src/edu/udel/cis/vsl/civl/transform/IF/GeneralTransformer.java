package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.GeneralWorker;

public class GeneralTransformer extends BaseTransformer {

	public final static String CODE = "general";
	public final static String LONG_NAME = "GeneralTransformer";
	public final static String SHORT_DESCRIPTION = "transforms general features of C programs to CIVL-C";

	public GeneralTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new GeneralWorker(astFactory).transform(ast);
	}

}
