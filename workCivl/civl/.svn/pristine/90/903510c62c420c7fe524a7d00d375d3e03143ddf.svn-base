package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.OpenMPOrphanWorker;

public class OpenMPOrphanTransformer extends BaseTransformer {
	/**
	 * The code (short name) of this transformer.
	 */
	public final static String CODE = "openmp_orphan";

	/**
	 * The long name of the transformer.
	 */
	public static String LONG_NAME = "OpenMPOrphanTransformer";

	/**
	 * The description of this transformer.
	 */
	public static String SHORT_DESCRIPTION = "transforms away orphan constructs of C/OpenMP programs";

	/**
	 * Creates a new instance of OpenMP2CIVLTransformer.
	 * 
	 * @param astFactory
	 *            The ASTFactory that will be used to create new nodes.
	 */
	public OpenMPOrphanTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new OpenMPOrphanWorker(astFactory).transform(ast);
	}

}
