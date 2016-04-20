package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.SvcompWorker;

/**
 * Transforms svcomp programs which are preprocessed by GCC
 * 
 * @author Manchun Zheng
 *
 */
public class SvcompTransformer extends BaseTransformer {

	/**
	 * The code (short name) of this transformer.
	 */
	public final static String CODE = "svcomp";

	/**
	 * The long name of the transformer.
	 */
	public static String LONG_NAME = "SvcompTransformer";

	/**
	 * The description of this transformer.
	 */
	public static String SHORT_DESCRIPTION = "transforms (unpreprocessed) programs from SVCOMP benchmarks to CIVL-C";

	public SvcompTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new SvcompWorker(astFactory).transform(ast);
	}

}
