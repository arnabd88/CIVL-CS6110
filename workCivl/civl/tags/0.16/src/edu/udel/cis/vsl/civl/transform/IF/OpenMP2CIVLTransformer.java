package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.OpenMP2CIVLWorker;

/**
 * OpenMP2CIVLTransformer transforms an AST of an OpenMP program into an AST of
 * an equivalent CIVL-C program. See {@linkplain #transform(AST)}.
 * 
 * @author Michael Rogers
 * 
 */
public class OpenMP2CIVLTransformer extends BaseTransformer {

	/**
	 * The code (short name) of this transformer.
	 */
	public final static String CODE = "openmp";

	/**
	 * The long name of the transformer.
	 */
	public static String LONG_NAME = "OpenMPTransformer";

	/**
	 * The description of this transformer.
	 */
	public static String SHORT_DESCRIPTION = "transforms C/OpenMP program to CIVL-C";

	/**
	 * Creates a new instance of OpenMP2CIVLTransformer.
	 * 
	 * @param astFactory
	 *            The ASTFactory that will be used to create new nodes.
	 */
	public OpenMP2CIVLTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new OpenMP2CIVLWorker(astFactory).transform(ast);
	}

}
