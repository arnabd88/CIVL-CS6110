package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.MacroWorker;

public class MacroTransformer extends BaseTransformer {

	public final static String CODE = "macro";
	public final static String LONG_NAME = "MacroTransformer";
	public final static String SHORT_DESCRIPTION = "recovers macros from C programs to CIVL-C";

	public MacroTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new MacroWorker(astFactory).transform(ast);
	}
}
