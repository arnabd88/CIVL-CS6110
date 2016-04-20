package edu.udel.cis.vsl.abc.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public interface Combiner {

	/**
	 * Combine two ASTs into a single AST.
	 * 
	 * @param ast0
	 *            The first AST being combined.
	 * @param ast1
	 *            The second AST being combined.
	 * @return The AST representing the combination of ast0 and ast1.
	 * @throws SyntaxException
	 *             If it encounters an error in the ASTs or an unhandled case.
	 */
	AST combine(AST ast0, AST ast1) throws SyntaxException;

}
